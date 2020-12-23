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
% DateTime   : Thu Dec  3 12:23:43 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_4449)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f60,plain,(
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
     => ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK5)
        & ! [X3] :
            ( k1_funct_1(sK5,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(X1))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
            ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k4_tmap_1(X0,sK4),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(sK4))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
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
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k4_tmap_1(sK3,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
    & ! [X3] :
        ( k1_funct_1(sK5,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f60,f59,f58])).

fof(f96,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
        & r2_hidden(sK1(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
                        & r2_hidden(sK1(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f53])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | m1_subset_1(sK1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f91,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f93,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f94,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f95,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f14,axiom,(
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

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(flattening,[],[f33])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f56,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK2(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK2(X0,X1,X2,X3,X4))
        & r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK2(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK2(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK2(X0,X1,X2,X3,X4))
                        & r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(X2))
                        & m1_subset_1(sK2(X0,X1,X2,X3,X4),u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f56])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | m1_subset_1(sK2(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f69])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK2(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    ! [X3] :
      ( k1_funct_1(sK5,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK4))
      | ~ m1_subset_1(X3,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2742,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2739,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2730,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | m1_subset_1(sK1(X1,X2,X0,X4,X3),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2747,plain,
    ( k2_partfun1(X0,X1,X2,X3) = X4
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X3,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) = iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2752,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4344,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0)
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_2752])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_39,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_40,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_41,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_42,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_43,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_399,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_12,c_14])).

cnf(c_2808,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_2809,plain,
    ( v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2808])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2910,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2911,plain,
    ( m1_pre_topc(sK4,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2910])).

cnf(c_2913,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2911])).

cnf(c_4524,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4344,c_39,c_40,c_41,c_42,c_43,c_2809,c_2913])).

cnf(c_4795,plain,
    ( k2_partfun1(u1_struct_0(sK4),X0,X1,X2) = X3
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3))
    | v1_funct_2(X3,X2,X0) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK4),X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2747,c_4524])).

cnf(c_5002,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK4),X0) != iProver_top
    | v1_funct_2(X3,X2,X0) != iProver_top
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3))
    | k2_partfun1(u1_struct_0(sK4),X0,X1,X2) = X3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4795,c_39,c_40,c_41,c_2809,c_2913])).

cnf(c_5003,plain,
    ( k2_partfun1(u1_struct_0(sK4),X0,X1,X2) = X3
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3))
    | v1_funct_2(X3,X2,X0) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK4),X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5002])).

cnf(c_5009,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = X1
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1))
    | v1_funct_2(X1,X0,u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_5003])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_81,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_83,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_85,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_87,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_5047,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_funct_2(X1,X0,u1_struct_0(sK3)) != iProver_top
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1))
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5009,c_37,c_39,c_42,c_43,c_83,c_87])).

cnf(c_5048,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = X1
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1))
    | v1_funct_2(X1,X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5047])).

cnf(c_5054,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4)) = sK5
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5))
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_5048])).

cnf(c_2727,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2753,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2737,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3906,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2753,c_2737])).

cnf(c_3909,plain,
    ( m1_pre_topc(sK4,sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_3906])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_38,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3030,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3506,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | m1_pre_topc(sK4,sK4)
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_3507,plain,
    ( m1_pre_topc(sK4,X0) != iProver_top
    | m1_pre_topc(sK4,sK4) = iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3506])).

cnf(c_3509,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | m1_pre_topc(sK4,sK4) = iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3507])).

cnf(c_3828,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3829,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3828])).

cnf(c_4039,plain,
    ( m1_pre_topc(sK4,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3909,c_38,c_39,c_41,c_3509,c_3829])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2743,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4433,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK3,sK5,X0)
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_2743])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3006,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3007,plain,
    ( m1_pre_topc(sK4,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3006])).

cnf(c_3009,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3007])).

cnf(c_4535,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK3,sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4433,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_2913,c_3009])).

cnf(c_4536,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK3,sK5,X0)
    | m1_pre_topc(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4535])).

cnf(c_4541,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK4,sK3,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_4039,c_4536])).

cnf(c_5056,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5))
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5054,c_4541])).

cnf(c_5065,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5))
    | k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5056,c_39,c_40,c_41,c_42,c_43,c_2809,c_2913])).

cnf(c_5066,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5))
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5065])).

cnf(c_5069,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5))
    | m1_pre_topc(sK4,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_5066])).

cnf(c_2912,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2910])).

cnf(c_3508,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | m1_pre_topc(sK4,sK4)
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3506])).

cnf(c_5070,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5069])).

cnf(c_5372,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5069,c_35,c_34,c_32,c_2912,c_3508,c_3828,c_5070])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | k2_partfun1(X1,X2,X0,X4) = X3
    | k3_funct_2(X1,X2,X0,sK1(X1,X2,X0,X4,X3)) != k1_funct_1(X3,sK1(X1,X2,X0,X4,X3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2749,plain,
    ( k2_partfun1(X0,X1,X2,X3) = X4
    | k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X3,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5374,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
    | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4)) = sK5
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5372,c_2749])).

cnf(c_5375,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5374,c_4541])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5496,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5375,c_37,c_39,c_40,c_41,c_42,c_43,c_44,c_83,c_87,c_2809,c_2913])).

cnf(c_5500,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
    | m1_pre_topc(sK4,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_5496])).

cnf(c_5902,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5500,c_38,c_39,c_41,c_2913,c_3509,c_3829])).

cnf(c_24,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | r2_hidden(sK2(X1,X2,X0,X3,X4),u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2735,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4) = iProver_top
    | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) != iProver_top
    | r2_hidden(sK2(X1,X2,X0,X3,X4),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5908,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5902,c_2735])).

cnf(c_7467,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5908,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_2913,c_3009,c_3509,c_3829])).

cnf(c_7468,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7467])).

cnf(c_25,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | m1_subset_1(sK2(X1,X2,X0,X3,X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2734,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4) = iProver_top
    | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK2(X1,X2,X0,X3,X4),u1_struct_0(X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2744,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4240,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4) = iProver_top
    | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X2,X5) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK2(X1,X2,X0,X3,X4),u1_struct_0(X5)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X5) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_2744])).

cnf(c_6538,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(X1)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5902,c_4240])).

cnf(c_5909,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5902,c_2734])).

cnf(c_8478,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5909,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_2913,c_3009,c_3509,c_3829])).

cnf(c_8479,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8478])).

cnf(c_8485,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8479,c_2744])).

cnf(c_8523,plain,
    ( v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6538,c_40,c_8485])).

cnf(c_8524,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8523])).

cnf(c_8530,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8524,c_2744])).

cnf(c_8624,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_8530])).

cnf(c_8630,plain,
    ( v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8624,c_37,c_38,c_39,c_40,c_41,c_2913,c_3509,c_3829])).

cnf(c_8631,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8630])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2733,plain,
    ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8638,plain,
    ( k1_funct_1(k4_tmap_1(sK3,X0),sK2(sK3,sK4,sK4,sK5,X1)) = sK2(sK3,sK4,sK4,sK5,X1)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X1) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(sK2(sK3,sK4,sK4,sK5,X1),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8631,c_2733])).

cnf(c_8798,plain,
    ( v2_struct_0(X0) = iProver_top
    | r2_hidden(sK2(sK3,sK4,sK4,sK5,X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X1) = iProver_top
    | k1_funct_1(k4_tmap_1(sK3,X0),sK2(sK3,sK4,sK4,sK5,X1)) = sK2(sK3,sK4,sK4,sK5,X1)
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8638,c_37,c_38,c_39])).

cnf(c_8799,plain,
    ( k1_funct_1(k4_tmap_1(sK3,X0),sK2(sK3,sK4,sK4,sK5,X1)) = sK2(sK3,sK4,sK4,sK5,X1)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X1) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(sK2(sK3,sK4,sK4,sK5,X1),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8798])).

cnf(c_8804,plain,
    ( k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7468,c_8799])).

cnf(c_8872,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8804,c_40,c_41])).

cnf(c_8873,plain,
    ( k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8872])).

cnf(c_8878,plain,
    ( k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2742,c_8873])).

cnf(c_27,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_108,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_112,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2098,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_2116,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2883,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v1_funct_1(k4_tmap_1(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2997,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v1_funct_1(k4_tmap_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2883])).

cnf(c_2998,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k4_tmap_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2997])).

cnf(c_18,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2870,plain,
    ( v1_funct_2(k4_tmap_1(sK3,X0),u1_struct_0(X0),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3018,plain,
    ( v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2870])).

cnf(c_3019,plain,
    ( v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3018])).

cnf(c_2081,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3505,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2081])).

cnf(c_6,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2751,plain,
    ( r2_funct_2(X0,X1,X2,X2) = iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3656,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_2751])).

cnf(c_3657,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3656])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2738,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4047,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_2738])).

cnf(c_4103,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4047,c_38,c_39])).

cnf(c_2754,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4109,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4103,c_2754])).

cnf(c_4115,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4)
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2753,c_4109])).

cnf(c_7,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2750,plain,
    ( X0 = X1
    | r2_funct_2(X2,X3,X1,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X0,X2,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4353,plain,
    ( sK5 = X0
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_2750])).

cnf(c_4441,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | sK5 = X0
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4353,c_42,c_43])).

cnf(c_4442,plain,
    ( sK5 = X0
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4441])).

cnf(c_4447,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2742,c_4442])).

cnf(c_4724,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4447,c_37,c_38,c_39,c_41,c_2998,c_3019])).

cnf(c_2093,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | r2_funct_2(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_2802,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
    | k4_tmap_1(sK3,sK4) != X2
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK4) != X0
    | sK5 != X3 ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_3075,plain,
    ( ~ r2_funct_2(X0,X1,X2,sK5)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
    | k4_tmap_1(sK3,sK4) != X2
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK4) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2802])).

cnf(c_3989,plain,
    ( ~ r2_funct_2(X0,u1_struct_0(sK3),X1,sK5)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
    | k4_tmap_1(sK3,sK4) != X1
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3075])).

cnf(c_5826,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0,sK5)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
    | k4_tmap_1(sK3,sK4) != X0
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3989])).

cnf(c_9047,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)
    | k4_tmap_1(sK3,sK4) != sK5
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_5826])).

cnf(c_9174,plain,
    ( k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8878,c_36,c_35,c_38,c_34,c_39,c_32,c_41,c_31,c_30,c_27,c_108,c_112,c_2116,c_2997,c_3018,c_3505,c_3509,c_3657,c_3829,c_4115,c_4449,c_8881,c_9047])).

cnf(c_4530,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(X0,sK4,X1,X2,X3)) = k1_funct_1(sK5,sK2(X0,sK4,X1,X2,X3))
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK4,X0,X2,X1),X3) = iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_4524])).

cnf(c_4745,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK4,X0,X2,X1),X3) = iProver_top
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(X0,sK4,X1,X2,X3)) = k1_funct_1(sK5,sK2(X0,sK4,X1,X2,X3))
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4530,c_38,c_39,c_40,c_41,c_2913,c_3009])).

cnf(c_4746,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(X0,sK4,X1,X2,X3)) = k1_funct_1(sK5,sK2(X0,sK4,X1,X2,X3))
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK4,X0,X2,X1),X3) = iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4745])).

cnf(c_5910,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,X0)) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5902,c_4746])).

cnf(c_6139,plain,
    ( v1_funct_1(X0) != iProver_top
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,X0)) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5910,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_3509,c_3829])).

cnf(c_6140,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,X0)) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6139])).

cnf(c_6145,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2742,c_6140])).

cnf(c_6399,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6145,c_37,c_38,c_39,c_41,c_2998,c_3019])).

cnf(c_6403,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)))
    | k4_tmap_1(sK3,sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_6399,c_4724])).

cnf(c_23,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK2(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK2(X1,X2,X0,X3,X4)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2736,plain,
    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X1,X0,X3,X2,X4)) != k1_funct_1(X4,sK2(X1,X0,X3,X2,X4))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X0,X1,X2,X3),X4) = iProver_top
    | v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6534,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) != k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK4,sK3,sK5,sK4),k4_tmap_1(sK3,sK4)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6403,c_2736])).

cnf(c_6535,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) != k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6534,c_5902])).

cnf(c_2881,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | m1_subset_1(k4_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3023,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2881])).

cnf(c_3024,plain,
    ( m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3023])).

cnf(c_8544,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) != k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6535,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_2913,c_2998,c_3009,c_3019,c_3024,c_3509,c_3829,c_4447])).

cnf(c_9176,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) != sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_9174,c_8544])).

cnf(c_28,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,u1_struct_0(sK4))
    | k1_funct_1(sK5,X0) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2731,plain,
    ( k1_funct_1(sK5,X0) = X0
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6542,plain,
    ( k1_funct_1(sK5,sK2(X0,X1,X2,X3,X4)) = sK2(X0,X1,X2,X3,X4)
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) = iProver_top
    | v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4240,c_2731])).

cnf(c_6763,plain,
    ( l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | k1_funct_1(sK5,sK2(X0,X1,X2,X3,X4)) = sK2(X0,X1,X2,X3,X4)
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) = iProver_top
    | v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6542,c_37,c_39])).

cnf(c_6764,plain,
    ( k1_funct_1(sK5,sK2(X0,X1,X2,X3,X4)) = sK2(X0,X1,X2,X3,X4)
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) = iProver_top
    | v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(renaming,[status(thm)],[c_6763])).

cnf(c_6767,plain,
    ( k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_pre_topc(sK4,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5902,c_6764])).

cnf(c_6982,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6767,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_2913,c_3009,c_3509,c_3829,c_5908])).

cnf(c_6983,plain,
    ( k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6982])).

cnf(c_6988,plain,
    ( k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2742,c_6983])).

cnf(c_7206,plain,
    ( k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6988,c_37,c_38,c_39,c_41,c_2998,c_3019])).

cnf(c_7210,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_7206,c_4724])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9176,c_9047,c_7210,c_4115,c_3829,c_3657,c_3509,c_3505,c_2116,c_112,c_108,c_27,c_30,c_31,c_41,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:17:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.02/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/0.98  
% 4.02/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.02/0.98  
% 4.02/0.98  ------  iProver source info
% 4.02/0.98  
% 4.02/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.02/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.02/0.98  git: non_committed_changes: false
% 4.02/0.98  git: last_make_outside_of_git: false
% 4.02/0.98  
% 4.02/0.98  ------ 
% 4.02/0.98  
% 4.02/0.98  ------ Input Options
% 4.02/0.98  
% 4.02/0.98  --out_options                           all
% 4.02/0.98  --tptp_safe_out                         true
% 4.02/0.98  --problem_path                          ""
% 4.02/0.98  --include_path                          ""
% 4.02/0.98  --clausifier                            res/vclausify_rel
% 4.02/0.98  --clausifier_options                    ""
% 4.02/0.98  --stdin                                 false
% 4.02/0.98  --stats_out                             all
% 4.02/0.98  
% 4.02/0.98  ------ General Options
% 4.02/0.98  
% 4.02/0.98  --fof                                   false
% 4.02/0.98  --time_out_real                         305.
% 4.02/0.98  --time_out_virtual                      -1.
% 4.02/0.98  --symbol_type_check                     false
% 4.02/0.98  --clausify_out                          false
% 4.02/0.98  --sig_cnt_out                           false
% 4.02/0.98  --trig_cnt_out                          false
% 4.02/0.98  --trig_cnt_out_tolerance                1.
% 4.02/0.98  --trig_cnt_out_sk_spl                   false
% 4.02/0.98  --abstr_cl_out                          false
% 4.02/0.98  
% 4.02/0.98  ------ Global Options
% 4.02/0.98  
% 4.02/0.98  --schedule                              default
% 4.02/0.98  --add_important_lit                     false
% 4.02/0.98  --prop_solver_per_cl                    1000
% 4.02/0.98  --min_unsat_core                        false
% 4.02/0.98  --soft_assumptions                      false
% 4.02/0.98  --soft_lemma_size                       3
% 4.02/0.98  --prop_impl_unit_size                   0
% 4.02/0.98  --prop_impl_unit                        []
% 4.02/0.98  --share_sel_clauses                     true
% 4.02/0.98  --reset_solvers                         false
% 4.02/0.98  --bc_imp_inh                            [conj_cone]
% 4.02/0.98  --conj_cone_tolerance                   3.
% 4.02/0.98  --extra_neg_conj                        none
% 4.02/0.98  --large_theory_mode                     true
% 4.02/0.98  --prolific_symb_bound                   200
% 4.02/0.98  --lt_threshold                          2000
% 4.02/0.98  --clause_weak_htbl                      true
% 4.02/0.98  --gc_record_bc_elim                     false
% 4.02/0.98  
% 4.02/0.98  ------ Preprocessing Options
% 4.02/0.98  
% 4.02/0.98  --preprocessing_flag                    true
% 4.02/0.98  --time_out_prep_mult                    0.1
% 4.02/0.98  --splitting_mode                        input
% 4.02/0.98  --splitting_grd                         true
% 4.02/0.98  --splitting_cvd                         false
% 4.02/0.98  --splitting_cvd_svl                     false
% 4.02/0.98  --splitting_nvd                         32
% 4.02/0.98  --sub_typing                            true
% 4.02/0.98  --prep_gs_sim                           true
% 4.02/0.98  --prep_unflatten                        true
% 4.02/0.98  --prep_res_sim                          true
% 4.02/0.98  --prep_upred                            true
% 4.02/0.98  --prep_sem_filter                       exhaustive
% 4.02/0.98  --prep_sem_filter_out                   false
% 4.02/0.98  --pred_elim                             true
% 4.02/0.98  --res_sim_input                         true
% 4.02/0.98  --eq_ax_congr_red                       true
% 4.02/0.98  --pure_diseq_elim                       true
% 4.02/0.98  --brand_transform                       false
% 4.02/0.98  --non_eq_to_eq                          false
% 4.02/0.98  --prep_def_merge                        true
% 4.02/0.98  --prep_def_merge_prop_impl              false
% 4.02/0.98  --prep_def_merge_mbd                    true
% 4.02/0.98  --prep_def_merge_tr_red                 false
% 4.02/0.98  --prep_def_merge_tr_cl                  false
% 4.02/0.98  --smt_preprocessing                     true
% 4.02/0.98  --smt_ac_axioms                         fast
% 4.02/0.98  --preprocessed_out                      false
% 4.02/0.98  --preprocessed_stats                    false
% 4.02/0.98  
% 4.02/0.98  ------ Abstraction refinement Options
% 4.02/0.98  
% 4.02/0.98  --abstr_ref                             []
% 4.02/0.98  --abstr_ref_prep                        false
% 4.02/0.98  --abstr_ref_until_sat                   false
% 4.02/0.98  --abstr_ref_sig_restrict                funpre
% 4.02/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.98  --abstr_ref_under                       []
% 4.02/0.98  
% 4.02/0.98  ------ SAT Options
% 4.02/0.98  
% 4.02/0.98  --sat_mode                              false
% 4.02/0.98  --sat_fm_restart_options                ""
% 4.02/0.98  --sat_gr_def                            false
% 4.02/0.98  --sat_epr_types                         true
% 4.02/0.98  --sat_non_cyclic_types                  false
% 4.02/0.98  --sat_finite_models                     false
% 4.02/0.98  --sat_fm_lemmas                         false
% 4.02/0.98  --sat_fm_prep                           false
% 4.02/0.98  --sat_fm_uc_incr                        true
% 4.02/0.99  --sat_out_model                         small
% 4.02/0.99  --sat_out_clauses                       false
% 4.02/0.99  
% 4.02/0.99  ------ QBF Options
% 4.02/0.99  
% 4.02/0.99  --qbf_mode                              false
% 4.02/0.99  --qbf_elim_univ                         false
% 4.02/0.99  --qbf_dom_inst                          none
% 4.02/0.99  --qbf_dom_pre_inst                      false
% 4.02/0.99  --qbf_sk_in                             false
% 4.02/0.99  --qbf_pred_elim                         true
% 4.02/0.99  --qbf_split                             512
% 4.02/0.99  
% 4.02/0.99  ------ BMC1 Options
% 4.02/0.99  
% 4.02/0.99  --bmc1_incremental                      false
% 4.02/0.99  --bmc1_axioms                           reachable_all
% 4.02/0.99  --bmc1_min_bound                        0
% 4.02/0.99  --bmc1_max_bound                        -1
% 4.02/0.99  --bmc1_max_bound_default                -1
% 4.02/0.99  --bmc1_symbol_reachability              true
% 4.02/0.99  --bmc1_property_lemmas                  false
% 4.02/0.99  --bmc1_k_induction                      false
% 4.02/0.99  --bmc1_non_equiv_states                 false
% 4.02/0.99  --bmc1_deadlock                         false
% 4.02/0.99  --bmc1_ucm                              false
% 4.02/0.99  --bmc1_add_unsat_core                   none
% 4.02/0.99  --bmc1_unsat_core_children              false
% 4.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.99  --bmc1_out_stat                         full
% 4.02/0.99  --bmc1_ground_init                      false
% 4.02/0.99  --bmc1_pre_inst_next_state              false
% 4.02/0.99  --bmc1_pre_inst_state                   false
% 4.02/0.99  --bmc1_pre_inst_reach_state             false
% 4.02/0.99  --bmc1_out_unsat_core                   false
% 4.02/0.99  --bmc1_aig_witness_out                  false
% 4.02/0.99  --bmc1_verbose                          false
% 4.02/0.99  --bmc1_dump_clauses_tptp                false
% 4.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.99  --bmc1_dump_file                        -
% 4.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.99  --bmc1_ucm_extend_mode                  1
% 4.02/0.99  --bmc1_ucm_init_mode                    2
% 4.02/0.99  --bmc1_ucm_cone_mode                    none
% 4.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.99  --bmc1_ucm_relax_model                  4
% 4.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.99  --bmc1_ucm_layered_model                none
% 4.02/0.99  --bmc1_ucm_max_lemma_size               10
% 4.02/0.99  
% 4.02/0.99  ------ AIG Options
% 4.02/0.99  
% 4.02/0.99  --aig_mode                              false
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation Options
% 4.02/0.99  
% 4.02/0.99  --instantiation_flag                    true
% 4.02/0.99  --inst_sos_flag                         true
% 4.02/0.99  --inst_sos_phase                        true
% 4.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel_side                     num_symb
% 4.02/0.99  --inst_solver_per_active                1400
% 4.02/0.99  --inst_solver_calls_frac                1.
% 4.02/0.99  --inst_passive_queue_type               priority_queues
% 4.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.99  --inst_passive_queues_freq              [25;2]
% 4.02/0.99  --inst_dismatching                      true
% 4.02/0.99  --inst_eager_unprocessed_to_passive     true
% 4.02/0.99  --inst_prop_sim_given                   true
% 4.02/0.99  --inst_prop_sim_new                     false
% 4.02/0.99  --inst_subs_new                         false
% 4.02/0.99  --inst_eq_res_simp                      false
% 4.02/0.99  --inst_subs_given                       false
% 4.02/0.99  --inst_orphan_elimination               true
% 4.02/0.99  --inst_learning_loop_flag               true
% 4.02/0.99  --inst_learning_start                   3000
% 4.02/0.99  --inst_learning_factor                  2
% 4.02/0.99  --inst_start_prop_sim_after_learn       3
% 4.02/0.99  --inst_sel_renew                        solver
% 4.02/0.99  --inst_lit_activity_flag                true
% 4.02/0.99  --inst_restr_to_given                   false
% 4.02/0.99  --inst_activity_threshold               500
% 4.02/0.99  --inst_out_proof                        true
% 4.02/0.99  
% 4.02/0.99  ------ Resolution Options
% 4.02/0.99  
% 4.02/0.99  --resolution_flag                       true
% 4.02/0.99  --res_lit_sel                           adaptive
% 4.02/0.99  --res_lit_sel_side                      none
% 4.02/0.99  --res_ordering                          kbo
% 4.02/0.99  --res_to_prop_solver                    active
% 4.02/0.99  --res_prop_simpl_new                    false
% 4.02/0.99  --res_prop_simpl_given                  true
% 4.02/0.99  --res_passive_queue_type                priority_queues
% 4.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.99  --res_passive_queues_freq               [15;5]
% 4.02/0.99  --res_forward_subs                      full
% 4.02/0.99  --res_backward_subs                     full
% 4.02/0.99  --res_forward_subs_resolution           true
% 4.02/0.99  --res_backward_subs_resolution          true
% 4.02/0.99  --res_orphan_elimination                true
% 4.02/0.99  --res_time_limit                        2.
% 4.02/0.99  --res_out_proof                         true
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Options
% 4.02/0.99  
% 4.02/0.99  --superposition_flag                    true
% 4.02/0.99  --sup_passive_queue_type                priority_queues
% 4.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.99  --demod_completeness_check              fast
% 4.02/0.99  --demod_use_ground                      true
% 4.02/0.99  --sup_to_prop_solver                    passive
% 4.02/0.99  --sup_prop_simpl_new                    true
% 4.02/0.99  --sup_prop_simpl_given                  true
% 4.02/0.99  --sup_fun_splitting                     true
% 4.02/0.99  --sup_smt_interval                      50000
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Simplification Setup
% 4.02/0.99  
% 4.02/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.02/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_immed_triv                        [TrivRules]
% 4.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_bw_main                     []
% 4.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_input_bw                          []
% 4.02/0.99  
% 4.02/0.99  ------ Combination Options
% 4.02/0.99  
% 4.02/0.99  --comb_res_mult                         3
% 4.02/0.99  --comb_sup_mult                         2
% 4.02/0.99  --comb_inst_mult                        10
% 4.02/0.99  
% 4.02/0.99  ------ Debug Options
% 4.02/0.99  
% 4.02/0.99  --dbg_backtrace                         false
% 4.02/0.99  --dbg_dump_prop_clauses                 false
% 4.02/0.99  --dbg_dump_prop_clauses_file            -
% 4.02/0.99  --dbg_out_stat                          false
% 4.02/0.99  ------ Parsing...
% 4.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.99  ------ Proving...
% 4.02/0.99  ------ Problem Properties 
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  clauses                                 35
% 4.02/0.99  conjectures                             10
% 4.02/0.99  EPR                                     11
% 4.02/0.99  Horn                                    21
% 4.02/0.99  unary                                   10
% 4.02/0.99  binary                                  2
% 4.02/0.99  lits                                    187
% 4.02/0.99  lits eq                                 11
% 4.02/0.99  fd_pure                                 0
% 4.02/0.99  fd_pseudo                               0
% 4.02/0.99  fd_cond                                 0
% 4.02/0.99  fd_pseudo_cond                          5
% 4.02/0.99  AC symbols                              0
% 4.02/0.99  
% 4.02/0.99  ------ Schedule dynamic 5 is on 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  Current options:
% 4.02/0.99  ------ 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options
% 4.02/0.99  
% 4.02/0.99  --out_options                           all
% 4.02/0.99  --tptp_safe_out                         true
% 4.02/0.99  --problem_path                          ""
% 4.02/0.99  --include_path                          ""
% 4.02/0.99  --clausifier                            res/vclausify_rel
% 4.02/0.99  --clausifier_options                    ""
% 4.02/0.99  --stdin                                 false
% 4.02/0.99  --stats_out                             all
% 4.02/0.99  
% 4.02/0.99  ------ General Options
% 4.02/0.99  
% 4.02/0.99  --fof                                   false
% 4.02/0.99  --time_out_real                         305.
% 4.02/0.99  --time_out_virtual                      -1.
% 4.02/0.99  --symbol_type_check                     false
% 4.02/0.99  --clausify_out                          false
% 4.02/0.99  --sig_cnt_out                           false
% 4.02/0.99  --trig_cnt_out                          false
% 4.02/0.99  --trig_cnt_out_tolerance                1.
% 4.02/0.99  --trig_cnt_out_sk_spl                   false
% 4.02/0.99  --abstr_cl_out                          false
% 4.02/0.99  
% 4.02/0.99  ------ Global Options
% 4.02/0.99  
% 4.02/0.99  --schedule                              default
% 4.02/0.99  --add_important_lit                     false
% 4.02/0.99  --prop_solver_per_cl                    1000
% 4.02/0.99  --min_unsat_core                        false
% 4.02/0.99  --soft_assumptions                      false
% 4.02/0.99  --soft_lemma_size                       3
% 4.02/0.99  --prop_impl_unit_size                   0
% 4.02/0.99  --prop_impl_unit                        []
% 4.02/0.99  --share_sel_clauses                     true
% 4.02/0.99  --reset_solvers                         false
% 4.02/0.99  --bc_imp_inh                            [conj_cone]
% 4.02/0.99  --conj_cone_tolerance                   3.
% 4.02/0.99  --extra_neg_conj                        none
% 4.02/0.99  --large_theory_mode                     true
% 4.02/0.99  --prolific_symb_bound                   200
% 4.02/0.99  --lt_threshold                          2000
% 4.02/0.99  --clause_weak_htbl                      true
% 4.02/0.99  --gc_record_bc_elim                     false
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing Options
% 4.02/0.99  
% 4.02/0.99  --preprocessing_flag                    true
% 4.02/0.99  --time_out_prep_mult                    0.1
% 4.02/0.99  --splitting_mode                        input
% 4.02/0.99  --splitting_grd                         true
% 4.02/0.99  --splitting_cvd                         false
% 4.02/0.99  --splitting_cvd_svl                     false
% 4.02/0.99  --splitting_nvd                         32
% 4.02/0.99  --sub_typing                            true
% 4.02/0.99  --prep_gs_sim                           true
% 4.02/0.99  --prep_unflatten                        true
% 4.02/0.99  --prep_res_sim                          true
% 4.02/0.99  --prep_upred                            true
% 4.02/0.99  --prep_sem_filter                       exhaustive
% 4.02/0.99  --prep_sem_filter_out                   false
% 4.02/0.99  --pred_elim                             true
% 4.02/0.99  --res_sim_input                         true
% 4.02/0.99  --eq_ax_congr_red                       true
% 4.02/0.99  --pure_diseq_elim                       true
% 4.02/0.99  --brand_transform                       false
% 4.02/0.99  --non_eq_to_eq                          false
% 4.02/0.99  --prep_def_merge                        true
% 4.02/0.99  --prep_def_merge_prop_impl              false
% 4.02/0.99  --prep_def_merge_mbd                    true
% 4.02/0.99  --prep_def_merge_tr_red                 false
% 4.02/0.99  --prep_def_merge_tr_cl                  false
% 4.02/0.99  --smt_preprocessing                     true
% 4.02/0.99  --smt_ac_axioms                         fast
% 4.02/0.99  --preprocessed_out                      false
% 4.02/0.99  --preprocessed_stats                    false
% 4.02/0.99  
% 4.02/0.99  ------ Abstraction refinement Options
% 4.02/0.99  
% 4.02/0.99  --abstr_ref                             []
% 4.02/0.99  --abstr_ref_prep                        false
% 4.02/0.99  --abstr_ref_until_sat                   false
% 4.02/0.99  --abstr_ref_sig_restrict                funpre
% 4.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.99  --abstr_ref_under                       []
% 4.02/0.99  
% 4.02/0.99  ------ SAT Options
% 4.02/0.99  
% 4.02/0.99  --sat_mode                              false
% 4.02/0.99  --sat_fm_restart_options                ""
% 4.02/0.99  --sat_gr_def                            false
% 4.02/0.99  --sat_epr_types                         true
% 4.02/0.99  --sat_non_cyclic_types                  false
% 4.02/0.99  --sat_finite_models                     false
% 4.02/0.99  --sat_fm_lemmas                         false
% 4.02/0.99  --sat_fm_prep                           false
% 4.02/0.99  --sat_fm_uc_incr                        true
% 4.02/0.99  --sat_out_model                         small
% 4.02/0.99  --sat_out_clauses                       false
% 4.02/0.99  
% 4.02/0.99  ------ QBF Options
% 4.02/0.99  
% 4.02/0.99  --qbf_mode                              false
% 4.02/0.99  --qbf_elim_univ                         false
% 4.02/0.99  --qbf_dom_inst                          none
% 4.02/0.99  --qbf_dom_pre_inst                      false
% 4.02/0.99  --qbf_sk_in                             false
% 4.02/0.99  --qbf_pred_elim                         true
% 4.02/0.99  --qbf_split                             512
% 4.02/0.99  
% 4.02/0.99  ------ BMC1 Options
% 4.02/0.99  
% 4.02/0.99  --bmc1_incremental                      false
% 4.02/0.99  --bmc1_axioms                           reachable_all
% 4.02/0.99  --bmc1_min_bound                        0
% 4.02/0.99  --bmc1_max_bound                        -1
% 4.02/0.99  --bmc1_max_bound_default                -1
% 4.02/0.99  --bmc1_symbol_reachability              true
% 4.02/0.99  --bmc1_property_lemmas                  false
% 4.02/0.99  --bmc1_k_induction                      false
% 4.02/0.99  --bmc1_non_equiv_states                 false
% 4.02/0.99  --bmc1_deadlock                         false
% 4.02/0.99  --bmc1_ucm                              false
% 4.02/0.99  --bmc1_add_unsat_core                   none
% 4.02/0.99  --bmc1_unsat_core_children              false
% 4.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.99  --bmc1_out_stat                         full
% 4.02/0.99  --bmc1_ground_init                      false
% 4.02/0.99  --bmc1_pre_inst_next_state              false
% 4.02/0.99  --bmc1_pre_inst_state                   false
% 4.02/0.99  --bmc1_pre_inst_reach_state             false
% 4.02/0.99  --bmc1_out_unsat_core                   false
% 4.02/0.99  --bmc1_aig_witness_out                  false
% 4.02/0.99  --bmc1_verbose                          false
% 4.02/0.99  --bmc1_dump_clauses_tptp                false
% 4.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.99  --bmc1_dump_file                        -
% 4.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.99  --bmc1_ucm_extend_mode                  1
% 4.02/0.99  --bmc1_ucm_init_mode                    2
% 4.02/0.99  --bmc1_ucm_cone_mode                    none
% 4.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.99  --bmc1_ucm_relax_model                  4
% 4.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.99  --bmc1_ucm_layered_model                none
% 4.02/0.99  --bmc1_ucm_max_lemma_size               10
% 4.02/0.99  
% 4.02/0.99  ------ AIG Options
% 4.02/0.99  
% 4.02/0.99  --aig_mode                              false
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation Options
% 4.02/0.99  
% 4.02/0.99  --instantiation_flag                    true
% 4.02/0.99  --inst_sos_flag                         true
% 4.02/0.99  --inst_sos_phase                        true
% 4.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel_side                     none
% 4.02/0.99  --inst_solver_per_active                1400
% 4.02/0.99  --inst_solver_calls_frac                1.
% 4.02/0.99  --inst_passive_queue_type               priority_queues
% 4.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.99  --inst_passive_queues_freq              [25;2]
% 4.02/0.99  --inst_dismatching                      true
% 4.02/0.99  --inst_eager_unprocessed_to_passive     true
% 4.02/0.99  --inst_prop_sim_given                   true
% 4.02/0.99  --inst_prop_sim_new                     false
% 4.02/0.99  --inst_subs_new                         false
% 4.02/0.99  --inst_eq_res_simp                      false
% 4.02/0.99  --inst_subs_given                       false
% 4.02/0.99  --inst_orphan_elimination               true
% 4.02/0.99  --inst_learning_loop_flag               true
% 4.02/0.99  --inst_learning_start                   3000
% 4.02/0.99  --inst_learning_factor                  2
% 4.02/0.99  --inst_start_prop_sim_after_learn       3
% 4.02/0.99  --inst_sel_renew                        solver
% 4.02/0.99  --inst_lit_activity_flag                true
% 4.02/0.99  --inst_restr_to_given                   false
% 4.02/0.99  --inst_activity_threshold               500
% 4.02/0.99  --inst_out_proof                        true
% 4.02/0.99  
% 4.02/0.99  ------ Resolution Options
% 4.02/0.99  
% 4.02/0.99  --resolution_flag                       false
% 4.02/0.99  --res_lit_sel                           adaptive
% 4.02/0.99  --res_lit_sel_side                      none
% 4.02/0.99  --res_ordering                          kbo
% 4.02/0.99  --res_to_prop_solver                    active
% 4.02/0.99  --res_prop_simpl_new                    false
% 4.02/0.99  --res_prop_simpl_given                  true
% 4.02/0.99  --res_passive_queue_type                priority_queues
% 4.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.99  --res_passive_queues_freq               [15;5]
% 4.02/0.99  --res_forward_subs                      full
% 4.02/0.99  --res_backward_subs                     full
% 4.02/0.99  --res_forward_subs_resolution           true
% 4.02/0.99  --res_backward_subs_resolution          true
% 4.02/0.99  --res_orphan_elimination                true
% 4.02/0.99  --res_time_limit                        2.
% 4.02/0.99  --res_out_proof                         true
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Options
% 4.02/0.99  
% 4.02/0.99  --superposition_flag                    true
% 4.02/0.99  --sup_passive_queue_type                priority_queues
% 4.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.99  --demod_completeness_check              fast
% 4.02/0.99  --demod_use_ground                      true
% 4.02/0.99  --sup_to_prop_solver                    passive
% 4.02/0.99  --sup_prop_simpl_new                    true
% 4.02/0.99  --sup_prop_simpl_given                  true
% 4.02/0.99  --sup_fun_splitting                     true
% 4.02/0.99  --sup_smt_interval                      50000
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Simplification Setup
% 4.02/0.99  
% 4.02/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.02/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_immed_triv                        [TrivRules]
% 4.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_bw_main                     []
% 4.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_input_bw                          []
% 4.02/0.99  
% 4.02/0.99  ------ Combination Options
% 4.02/0.99  
% 4.02/0.99  --comb_res_mult                         3
% 4.02/0.99  --comb_sup_mult                         2
% 4.02/0.99  --comb_inst_mult                        10
% 4.02/0.99  
% 4.02/0.99  ------ Debug Options
% 4.02/0.99  
% 4.02/0.99  --dbg_backtrace                         false
% 4.02/0.99  --dbg_dump_prop_clauses                 false
% 4.02/0.99  --dbg_dump_prop_clauses_file            -
% 4.02/0.99  --dbg_out_stat                          false
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ Proving...
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS status Theorem for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  fof(f12,axiom,(
% 4.02/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f35,plain,(
% 4.02/0.99    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f12])).
% 4.02/0.99  
% 4.02/0.99  fof(f36,plain,(
% 4.02/0.99    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/0.99    inference(flattening,[],[f35])).
% 4.02/0.99  
% 4.02/0.99  fof(f81,plain,(
% 4.02/0.99    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f36])).
% 4.02/0.99  
% 4.02/0.99  fof(f13,axiom,(
% 4.02/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f37,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f13])).
% 4.02/0.99  
% 4.02/0.99  fof(f82,plain,(
% 4.02/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f37])).
% 4.02/0.99  
% 4.02/0.99  fof(f17,conjecture,(
% 4.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f18,negated_conjecture,(
% 4.02/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 4.02/0.99    inference(negated_conjecture,[],[f17])).
% 4.02/0.99  
% 4.02/0.99  fof(f44,plain,(
% 4.02/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f18])).
% 4.02/0.99  
% 4.02/0.99  fof(f45,plain,(
% 4.02/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.02/0.99    inference(flattening,[],[f44])).
% 4.02/0.99  
% 4.02/0.99  fof(f60,plain,(
% 4.02/0.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK5) & ! [X3] : (k1_funct_1(sK5,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f59,plain,(
% 4.02/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k4_tmap_1(X0,sK4),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f58,plain,(
% 4.02/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k4_tmap_1(sK3,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f61,plain,(
% 4.02/0.99    ((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5) & ! [X3] : (k1_funct_1(sK5,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f60,f59,f58])).
% 4.02/0.99  
% 4.02/0.99  fof(f96,plain,(
% 4.02/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f5,axiom,(
% 4.02/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X4,X3,X1) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,X0) => (r2_hidden(X5,X3) => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5))) => k2_partfun1(X0,X1,X2,X3) = X4))))))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f23,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(X0,X1,X2,X3) = X4 | ? [X5] : ((k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3)) & m1_subset_1(X5,X0))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f5])).
% 4.02/0.99  
% 4.02/0.99  fof(f24,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(X0,X1,X2,X3) = X4 | ? [X5] : (k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.02/0.99    inference(flattening,[],[f23])).
% 4.02/0.99  
% 4.02/0.99  fof(f53,plain,(
% 4.02/0.99    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,X3) & m1_subset_1(X5,X0)) => (k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4)) & r2_hidden(sK1(X0,X1,X2,X3,X4),X3) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0)))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f54,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(X0,X1,X2,X3) = X4 | (k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4)) & r2_hidden(sK1(X0,X1,X2,X3,X4),X3) & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f53])).
% 4.02/0.99  
% 4.02/0.99  fof(f70,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = X4 | m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f54])).
% 4.02/0.99  
% 4.02/0.99  fof(f3,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f19,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f3])).
% 4.02/0.99  
% 4.02/0.99  fof(f20,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 4.02/0.99    inference(flattening,[],[f19])).
% 4.02/0.99  
% 4.02/0.99  fof(f67,plain,(
% 4.02/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f20])).
% 4.02/0.99  
% 4.02/0.99  fof(f91,plain,(
% 4.02/0.99    l1_pre_topc(sK3)),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f92,plain,(
% 4.02/0.99    ~v2_struct_0(sK4)),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f93,plain,(
% 4.02/0.99    m1_pre_topc(sK4,sK3)),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f94,plain,(
% 4.02/0.99    v1_funct_1(sK5)),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f95,plain,(
% 4.02/0.99    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f7,axiom,(
% 4.02/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f27,plain,(
% 4.02/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f7])).
% 4.02/0.99  
% 4.02/0.99  fof(f74,plain,(
% 4.02/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f27])).
% 4.02/0.99  
% 4.02/0.99  fof(f9,axiom,(
% 4.02/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f29,plain,(
% 4.02/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f9])).
% 4.02/0.99  
% 4.02/0.99  fof(f30,plain,(
% 4.02/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 4.02/0.99    inference(flattening,[],[f29])).
% 4.02/0.99  
% 4.02/0.99  fof(f76,plain,(
% 4.02/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f30])).
% 4.02/0.99  
% 4.02/0.99  fof(f8,axiom,(
% 4.02/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f28,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f8])).
% 4.02/0.99  
% 4.02/0.99  fof(f75,plain,(
% 4.02/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f28])).
% 4.02/0.99  
% 4.02/0.99  fof(f89,plain,(
% 4.02/0.99    ~v2_struct_0(sK3)),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f2,axiom,(
% 4.02/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f50,plain,(
% 4.02/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.02/0.99    inference(nnf_transformation,[],[f2])).
% 4.02/0.99  
% 4.02/0.99  fof(f51,plain,(
% 4.02/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.02/0.99    inference(flattening,[],[f50])).
% 4.02/0.99  
% 4.02/0.99  fof(f64,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.02/0.99    inference(cnf_transformation,[],[f51])).
% 4.02/0.99  
% 4.02/0.99  fof(f100,plain,(
% 4.02/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.02/0.99    inference(equality_resolution,[],[f64])).
% 4.02/0.99  
% 4.02/0.99  fof(f14,axiom,(
% 4.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f38,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f14])).
% 4.02/0.99  
% 4.02/0.99  fof(f39,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.02/0.99    inference(flattening,[],[f38])).
% 4.02/0.99  
% 4.02/0.99  fof(f55,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.02/0.99    inference(nnf_transformation,[],[f39])).
% 4.02/0.99  
% 4.02/0.99  fof(f83,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f55])).
% 4.02/0.99  
% 4.02/0.99  fof(f90,plain,(
% 4.02/0.99    v2_pre_topc(sK3)),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f11,axiom,(
% 4.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f33,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f11])).
% 4.02/0.99  
% 4.02/0.99  fof(f34,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/0.99    inference(flattening,[],[f33])).
% 4.02/0.99  
% 4.02/0.99  fof(f78,plain,(
% 4.02/0.99    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f34])).
% 4.02/0.99  
% 4.02/0.99  fof(f6,axiom,(
% 4.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f25,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f6])).
% 4.02/0.99  
% 4.02/0.99  fof(f26,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.02/0.99    inference(flattening,[],[f25])).
% 4.02/0.99  
% 4.02/0.99  fof(f73,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f26])).
% 4.02/0.99  
% 4.02/0.99  fof(f72,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = X4 | k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X4,X3,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f54])).
% 4.02/0.99  
% 4.02/0.99  fof(f15,axiom,(
% 4.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f40,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f15])).
% 4.02/0.99  
% 4.02/0.99  fof(f41,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/0.99    inference(flattening,[],[f40])).
% 4.02/0.99  
% 4.02/0.99  fof(f56,plain,(
% 4.02/0.99    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK2(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK2(X0,X1,X2,X3,X4)) & r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK2(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f57,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK2(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK2(X0,X1,X2,X3,X4)) & r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK2(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f56])).
% 4.02/0.99  
% 4.02/0.99  fof(f86,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f57])).
% 4.02/0.99  
% 4.02/0.99  fof(f85,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK2(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f57])).
% 4.02/0.99  
% 4.02/0.99  fof(f10,axiom,(
% 4.02/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f31,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f10])).
% 4.02/0.99  
% 4.02/0.99  fof(f32,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/0.99    inference(flattening,[],[f31])).
% 4.02/0.99  
% 4.02/0.99  fof(f77,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f32])).
% 4.02/0.99  
% 4.02/0.99  fof(f16,axiom,(
% 4.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f42,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/0.99    inference(ennf_transformation,[],[f16])).
% 4.02/0.99  
% 4.02/0.99  fof(f43,plain,(
% 4.02/0.99    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/0.99    inference(flattening,[],[f42])).
% 4.02/0.99  
% 4.02/0.99  fof(f88,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f43])).
% 4.02/0.99  
% 4.02/0.99  fof(f98,plain,(
% 4.02/0.99    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  fof(f66,plain,(
% 4.02/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f51])).
% 4.02/0.99  
% 4.02/0.99  fof(f79,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f36])).
% 4.02/0.99  
% 4.02/0.99  fof(f80,plain,(
% 4.02/0.99    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f36])).
% 4.02/0.99  
% 4.02/0.99  fof(f4,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f21,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.02/0.99    inference(ennf_transformation,[],[f4])).
% 4.02/0.99  
% 4.02/0.99  fof(f22,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.02/0.99    inference(flattening,[],[f21])).
% 4.02/0.99  
% 4.02/0.99  fof(f52,plain,(
% 4.02/0.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.02/0.99    inference(nnf_transformation,[],[f22])).
% 4.02/0.99  
% 4.02/0.99  fof(f69,plain,(
% 4.02/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f52])).
% 4.02/0.99  
% 4.02/0.99  fof(f101,plain,(
% 4.02/0.99    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.02/0.99    inference(equality_resolution,[],[f69])).
% 4.02/0.99  
% 4.02/0.99  fof(f84,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f55])).
% 4.02/0.99  
% 4.02/0.99  fof(f68,plain,(
% 4.02/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f52])).
% 4.02/0.99  
% 4.02/0.99  fof(f87,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK2(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f57])).
% 4.02/0.99  
% 4.02/0.99  fof(f97,plain,(
% 4.02/0.99    ( ! [X3] : (k1_funct_1(sK5,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f61])).
% 4.02/0.99  
% 4.02/0.99  cnf(c_17,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.02/0.99      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.02/0.99      | v2_struct_0(X1)
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f81]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2742,plain,
% 4.02/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 4.02/0.99      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_20,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.02/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.02/0.99      | ~ l1_pre_topc(X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f82]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2739,plain,
% 4.02/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 4.02/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_29,negated_conjecture,
% 4.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 4.02/0.99      inference(cnf_transformation,[],[f96]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2730,plain,
% 4.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10,plain,
% 4.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.02/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.02/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
% 4.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.02/0.99      | m1_subset_1(sK1(X1,X2,X0,X4,X3),X1)
% 4.02/0.99      | ~ v1_funct_1(X0)
% 4.02/0.99      | ~ v1_funct_1(X3)
% 4.02/0.99      | v1_xboole_0(X1)
% 4.02/0.99      | v1_xboole_0(X2)
% 4.02/0.99      | v1_xboole_0(X4)
% 4.02/0.99      | k2_partfun1(X1,X2,X0,X4) = X3 ),
% 4.02/0.99      inference(cnf_transformation,[],[f70]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2747,plain,
% 4.02/0.99      ( k2_partfun1(X0,X1,X2,X3) = X4
% 4.02/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.02/0.99      | v1_funct_2(X4,X3,X1) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) = iProver_top
% 4.02/0.99      | v1_funct_1(X4) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top
% 4.02/0.99      | v1_xboole_0(X0) = iProver_top
% 4.02/0.99      | v1_xboole_0(X1) = iProver_top
% 4.02/0.99      | v1_xboole_0(X3) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5,plain,
% 4.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.02/0.99      | ~ m1_subset_1(X3,X1)
% 4.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | ~ v1_funct_1(X0)
% 4.02/0.99      | v1_xboole_0(X1)
% 4.02/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 4.02/0.99      inference(cnf_transformation,[],[f67]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2752,plain,
% 4.02/0.99      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 4.02/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,X0) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top
% 4.02/0.99      | v1_xboole_0(X0) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4344,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0)
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2730,c_2752]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_34,negated_conjecture,
% 4.02/0.99      ( l1_pre_topc(sK3) ),
% 4.02/0.99      inference(cnf_transformation,[],[f91]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_39,plain,
% 4.02/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_33,negated_conjecture,
% 4.02/0.99      ( ~ v2_struct_0(sK4) ),
% 4.02/0.99      inference(cnf_transformation,[],[f92]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_40,plain,
% 4.02/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_32,negated_conjecture,
% 4.02/0.99      ( m1_pre_topc(sK4,sK3) ),
% 4.02/0.99      inference(cnf_transformation,[],[f93]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_41,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_31,negated_conjecture,
% 4.02/0.99      ( v1_funct_1(sK5) ),
% 4.02/0.99      inference(cnf_transformation,[],[f94]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_42,plain,
% 4.02/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_30,negated_conjecture,
% 4.02/0.99      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f95]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_43,plain,
% 4.02/0.99      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_12,plain,
% 4.02/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_14,plain,
% 4.02/0.99      ( v2_struct_0(X0)
% 4.02/0.99      | ~ l1_struct_0(X0)
% 4.02/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_399,plain,
% 4.02/0.99      ( v2_struct_0(X0)
% 4.02/0.99      | ~ l1_pre_topc(X0)
% 4.02/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 4.02/0.99      inference(resolution,[status(thm)],[c_12,c_14]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2808,plain,
% 4.02/0.99      ( v2_struct_0(sK4)
% 4.02/0.99      | ~ l1_pre_topc(sK4)
% 4.02/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_399]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2809,plain,
% 4.02/0.99      ( v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2808]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_13,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f75]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2910,plain,
% 4.02/0.99      ( ~ m1_pre_topc(sK4,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK4) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2911,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,X0) != iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2910]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2913,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) = iProver_top ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2911]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4524,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0)
% 4.02/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_4344,c_39,c_40,c_41,c_42,c_43,c_2809,c_2913]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4795,plain,
% 4.02/0.99      ( k2_partfun1(u1_struct_0(sK4),X0,X1,X2) = X3
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3))
% 4.02/0.99      | v1_funct_2(X3,X2,X0) != iProver_top
% 4.02/0.99      | v1_funct_2(X1,u1_struct_0(sK4),X0) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X1) != iProver_top
% 4.02/0.99      | v1_xboole_0(X2) = iProver_top
% 4.02/0.99      | v1_xboole_0(X0) = iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2747,c_4524]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5002,plain,
% 4.02/0.99      ( v1_xboole_0(X0) = iProver_top
% 4.02/0.99      | v1_xboole_0(X2) = iProver_top
% 4.02/0.99      | v1_funct_1(X1) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.02/0.99      | v1_funct_2(X1,u1_struct_0(sK4),X0) != iProver_top
% 4.02/0.99      | v1_funct_2(X3,X2,X0) != iProver_top
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3))
% 4.02/0.99      | k2_partfun1(u1_struct_0(sK4),X0,X1,X2) = X3 ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_4795,c_39,c_40,c_41,c_2809,c_2913]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5003,plain,
% 4.02/0.99      ( k2_partfun1(u1_struct_0(sK4),X0,X1,X2) = X3
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),X0,X1,X2,X3))
% 4.02/0.99      | v1_funct_2(X3,X2,X0) != iProver_top
% 4.02/0.99      | v1_funct_2(X1,u1_struct_0(sK4),X0) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0))) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X1) != iProver_top
% 4.02/0.99      | v1_xboole_0(X2) = iProver_top
% 4.02/0.99      | v1_xboole_0(X0) = iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_5002]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5009,plain,
% 4.02/0.99      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = X1
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1))
% 4.02/0.99      | v1_funct_2(X1,X0,u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 4.02/0.99      | v1_funct_1(X1) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top
% 4.02/0.99      | v1_xboole_0(X0) = iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2730,c_5003]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_36,negated_conjecture,
% 4.02/0.99      ( ~ v2_struct_0(sK3) ),
% 4.02/0.99      inference(cnf_transformation,[],[f89]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_37,plain,
% 4.02/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_81,plain,
% 4.02/0.99      ( v2_struct_0(X0) = iProver_top
% 4.02/0.99      | l1_struct_0(X0) != iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_83,plain,
% 4.02/0.99      ( v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_struct_0(sK3) != iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_81]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_85,plain,
% 4.02/0.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_87,plain,
% 4.02/0.99      ( l1_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_85]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5047,plain,
% 4.02/0.99      ( v1_xboole_0(X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X1,X0,u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1))
% 4.02/0.99      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = X1
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 4.02/0.99      | v1_funct_1(X1) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_5009,c_37,c_39,c_42,c_43,c_83,c_87]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5048,plain,
% 4.02/0.99      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = X1
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0,X1))
% 4.02/0.99      | v1_funct_2(X1,X0,u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 4.02/0.99      | v1_funct_1(X1) != iProver_top
% 4.02/0.99      | v1_xboole_0(X0) = iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_5047]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5054,plain,
% 4.02/0.99      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4)) = sK5
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5))
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2730,c_5048]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2727,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4,plain,
% 4.02/0.99      ( r1_tarski(X0,X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f100]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2753,plain,
% 4.02/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_22,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.02/0.99      | ~ m1_pre_topc(X2,X1)
% 4.02/0.99      | m1_pre_topc(X0,X2)
% 4.02/0.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2737,plain,
% 4.02/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 4.02/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 4.02/0.99      | m1_pre_topc(X0,X2) = iProver_top
% 4.02/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3906,plain,
% 4.02/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 4.02/0.99      | m1_pre_topc(X0,X0) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2753,c_2737]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3909,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2727,c_3906]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_35,negated_conjecture,
% 4.02/0.99      ( v2_pre_topc(sK3) ),
% 4.02/0.99      inference(cnf_transformation,[],[f90]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_38,plain,
% 4.02/0.99      ( v2_pre_topc(sK3) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3030,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.02/0.99      | m1_pre_topc(X0,sK4)
% 4.02/0.99      | ~ m1_pre_topc(sK4,X1)
% 4.02/0.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X1) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3506,plain,
% 4.02/0.99      ( ~ m1_pre_topc(sK4,X0)
% 4.02/0.99      | m1_pre_topc(sK4,sK4)
% 4.02/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 4.02/0.99      | ~ l1_pre_topc(X0)
% 4.02/0.99      | ~ v2_pre_topc(X0) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_3030]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3507,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,X0) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) = iProver_top
% 4.02/0.99      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3506]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3509,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) = iProver_top
% 4.02/0.99      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_3507]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3828,plain,
% 4.02/0.99      ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3829,plain,
% 4.02/0.99      ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3828]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4039,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,sK4) = iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_3909,c_38,c_39,c_41,c_3509,c_3829]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_16,plain,
% 4.02/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.02/0.99      | ~ m1_pre_topc(X3,X1)
% 4.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.02/0.99      | v2_struct_0(X1)
% 4.02/0.99      | v2_struct_0(X2)
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ l1_pre_topc(X2)
% 4.02/0.99      | ~ v2_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X2)
% 4.02/0.99      | ~ v1_funct_1(X0)
% 4.02/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 4.02/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2743,plain,
% 4.02/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 4.02/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4433,plain,
% 4.02/0.99      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK3,sK5,X0)
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X0,sK4) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2730,c_2743]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_11,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X1)
% 4.02/0.99      | v2_pre_topc(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3006,plain,
% 4.02/0.99      ( ~ m1_pre_topc(sK4,X0)
% 4.02/0.99      | ~ l1_pre_topc(X0)
% 4.02/0.99      | ~ v2_pre_topc(X0)
% 4.02/0.99      | v2_pre_topc(sK4) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3007,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,X0) != iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK4) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3006]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3009,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK4) = iProver_top ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_3007]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4535,plain,
% 4.02/0.99      ( m1_pre_topc(X0,sK4) != iProver_top
% 4.02/0.99      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK3,sK5,X0) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_4433,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_2913,c_3009]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4536,plain,
% 4.02/0.99      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k2_tmap_1(sK4,sK3,sK5,X0)
% 4.02/0.99      | m1_pre_topc(X0,sK4) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_4535]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4541,plain,
% 4.02/0.99      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK4,sK3,sK5,sK4) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_4039,c_4536]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5056,plain,
% 4.02/0.99      ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5))
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 4.02/0.99      inference(demodulation,[status(thm)],[c_5054,c_4541]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5065,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5))
% 4.02/0.99      | k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
% 4.02/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_5056,c_39,c_40,c_41,c_42,c_43,c_2809,c_2913]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5066,plain,
% 4.02/0.99      ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5))
% 4.02/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_5065]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5069,plain,
% 4.02/0.99      ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5))
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2739,c_5066]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2912,plain,
% 4.02/0.99      ( ~ m1_pre_topc(sK4,sK3) | ~ l1_pre_topc(sK3) | l1_pre_topc(sK4) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2910]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3508,plain,
% 4.02/0.99      ( ~ m1_pre_topc(sK4,sK3)
% 4.02/0.99      | m1_pre_topc(sK4,sK4)
% 4.02/0.99      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 4.02/0.99      | ~ l1_pre_topc(sK3)
% 4.02/0.99      | ~ v2_pre_topc(sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_3506]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5070,plain,
% 4.02/0.99      ( ~ m1_pre_topc(sK4,sK4)
% 4.02/0.99      | ~ l1_pre_topc(sK4)
% 4.02/0.99      | k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) ),
% 4.02/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5069]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5372,plain,
% 4.02/0.99      ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) = k1_funct_1(sK5,sK1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4),sK5)) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_5069,c_35,c_34,c_32,c_2912,c_3508,c_3828,c_5070]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8,plain,
% 4.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.02/0.99      | ~ v1_funct_2(X3,X4,X2)
% 4.02/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
% 4.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.02/0.99      | ~ v1_funct_1(X0)
% 4.02/0.99      | ~ v1_funct_1(X3)
% 4.02/0.99      | v1_xboole_0(X1)
% 4.02/0.99      | v1_xboole_0(X2)
% 4.02/0.99      | v1_xboole_0(X4)
% 4.02/0.99      | k2_partfun1(X1,X2,X0,X4) = X3
% 4.02/0.99      | k3_funct_2(X1,X2,X0,sK1(X1,X2,X0,X4,X3)) != k1_funct_1(X3,sK1(X1,X2,X0,X4,X3)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f72]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2749,plain,
% 4.02/0.99      ( k2_partfun1(X0,X1,X2,X3) = X4
% 4.02/0.99      | k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
% 4.02/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.02/0.99      | v1_funct_2(X4,X3,X1) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(X0)) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 4.02/0.99      | v1_funct_1(X4) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top
% 4.02/0.99      | v1_xboole_0(X0) = iProver_top
% 4.02/0.99      | v1_xboole_0(X1) = iProver_top
% 4.02/0.99      | v1_xboole_0(X3) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5374,plain,
% 4.02/0.99      ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
% 4.02/0.99      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4)) = sK5
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_5372,c_2749]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5375,plain,
% 4.02/0.99      ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 4.02/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 4.02/0.99      inference(demodulation,[status(thm)],[c_5374,c_4541]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_44,plain,
% 4.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5496,plain,
% 4.02/0.99      ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
% 4.02/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_5375,c_37,c_39,c_40,c_41,c_42,c_43,c_44,c_83,c_87,
% 4.02/0.99                 c_2809,c_2913]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5500,plain,
% 4.02/0.99      ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2739,c_5496]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5902,plain,
% 4.02/0.99      ( k2_tmap_1(sK4,sK3,sK5,sK4) = sK5 ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_5500,c_38,c_39,c_41,c_2913,c_3509,c_3829]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_24,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 4.02/0.99      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 4.02/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 4.02/0.99      | ~ m1_pre_topc(X0,X2)
% 4.02/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 4.02/0.99      | r2_hidden(sK2(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 4.02/0.99      | v2_struct_0(X1)
% 4.02/0.99      | v2_struct_0(X2)
% 4.02/0.99      | v2_struct_0(X0)
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ l1_pre_topc(X2)
% 4.02/0.99      | ~ v2_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X2)
% 4.02/0.99      | ~ v1_funct_1(X3)
% 4.02/0.99      | ~ v1_funct_1(X4) ),
% 4.02/0.99      inference(cnf_transformation,[],[f86]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2735,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4) = iProver_top
% 4.02/0.99      | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 4.02/0.99      | v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) != iProver_top
% 4.02/0.99      | r2_hidden(sK2(X1,X2,X0,X3,X4),u1_struct_0(X0)) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v2_struct_0(X2) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | l1_pre_topc(X2) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_pre_topc(X2) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X4) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5908,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | r2_hidden(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_5902,c_2735]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7467,plain,
% 4.02/0.99      ( v1_funct_1(X0) != iProver_top
% 4.02/0.99      | r2_hidden(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_5908,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_2913,
% 4.02/0.99                 c_3009,c_3509,c_3829]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7468,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | r2_hidden(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_7467]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_25,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 4.02/0.99      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 4.02/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 4.02/0.99      | ~ m1_pre_topc(X0,X2)
% 4.02/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 4.02/0.99      | m1_subset_1(sK2(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 4.02/0.99      | v2_struct_0(X1)
% 4.02/0.99      | v2_struct_0(X2)
% 4.02/0.99      | v2_struct_0(X0)
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ l1_pre_topc(X2)
% 4.02/0.99      | ~ v2_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X2)
% 4.02/0.99      | ~ v1_funct_1(X3)
% 4.02/0.99      | ~ v1_funct_1(X4) ),
% 4.02/0.99      inference(cnf_transformation,[],[f85]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2734,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4) = iProver_top
% 4.02/0.99      | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 4.02/0.99      | v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(X1,X2,X0,X3,X4),u1_struct_0(X2)) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v2_struct_0(X2) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | l1_pre_topc(X2) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_pre_topc(X2) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X4) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_15,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.02/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 4.02/0.99      | v2_struct_0(X1)
% 4.02/0.99      | v2_struct_0(X0)
% 4.02/0.99      | ~ l1_pre_topc(X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2744,plain,
% 4.02/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4240,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4) = iProver_top
% 4.02/0.99      | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 4.02/0.99      | v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 4.02/0.99      | m1_pre_topc(X2,X5) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(X1,X2,X0,X3,X4),u1_struct_0(X5)) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v2_struct_0(X2) = iProver_top
% 4.02/0.99      | v2_struct_0(X5) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | l1_pre_topc(X2) != iProver_top
% 4.02/0.99      | l1_pre_topc(X5) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_pre_topc(X2) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X4) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2734,c_2744]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6538,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,X1) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(X1)) = iProver_top
% 4.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_5902,c_4240]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5909,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
% 4.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_5902,c_2734]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8478,plain,
% 4.02/0.99      ( v1_funct_1(X0) != iProver_top
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_5909,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_2913,
% 4.02/0.99                 c_3009,c_3509,c_3829]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8479,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) = iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_8478]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8485,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,X1) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(X1)) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_8479,c_2744]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8523,plain,
% 4.02/0.99      ( v1_funct_1(X0) != iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,X1) != iProver_top
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(X1)) = iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_6538,c_40,c_8485]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8524,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,X1) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(X1)) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_8523]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8530,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X1,X2) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,X1) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(X2)) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(X2) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | l1_pre_topc(X2) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_8524,c_2744]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8624,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK3)) = iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2727,c_8530]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8630,plain,
% 4.02/0.99      ( v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK3)) = iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_8624,c_37,c_38,c_39,c_40,c_41,c_2913,c_3509,c_3829]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8631,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK3)) = iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_8630]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_26,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.02/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.02/0.99      | ~ r2_hidden(X2,u1_struct_0(X0))
% 4.02/0.99      | v2_struct_0(X1)
% 4.02/0.99      | v2_struct_0(X0)
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X1)
% 4.02/0.99      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 4.02/0.99      inference(cnf_transformation,[],[f88]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2733,plain,
% 4.02/0.99      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
% 4.02/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | r2_hidden(X2,u1_struct_0(X1)) != iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8638,plain,
% 4.02/0.99      ( k1_funct_1(k4_tmap_1(sK3,X0),sK2(sK3,sK4,sK4,sK5,X1)) = sK2(sK3,sK4,sK4,sK5,X1)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X1) = iProver_top
% 4.02/0.99      | v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | r2_hidden(sK2(sK3,sK4,sK4,sK5,X1),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v1_funct_1(X1) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_8631,c_2733]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8798,plain,
% 4.02/0.99      ( v2_struct_0(X0) = iProver_top
% 4.02/0.99      | r2_hidden(sK2(sK3,sK4,sK4,sK5,X1),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 4.02/0.99      | v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X1) = iProver_top
% 4.02/0.99      | k1_funct_1(k4_tmap_1(sK3,X0),sK2(sK3,sK4,sK4,sK5,X1)) = sK2(sK3,sK4,sK4,sK5,X1)
% 4.02/0.99      | v1_funct_1(X1) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_8638,c_37,c_38,c_39]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8799,plain,
% 4.02/0.99      ( k1_funct_1(k4_tmap_1(sK3,X0),sK2(sK3,sK4,sK4,sK5,X1)) = sK2(sK3,sK4,sK4,sK5,X1)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X1) = iProver_top
% 4.02/0.99      | v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | r2_hidden(sK2(sK3,sK4,sK4,sK5,X1),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v1_funct_1(X1) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_8798]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8804,plain,
% 4.02/0.99      ( k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_7468,c_8799]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8872,plain,
% 4.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_8804,c_40,c_41]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8873,plain,
% 4.02/0.99      ( k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_8872]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8878,plain,
% 4.02/0.99      ( k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top
% 4.02/0.99      | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2742,c_8873]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_27,negated_conjecture,
% 4.02/0.99      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5) ),
% 4.02/0.99      inference(cnf_transformation,[],[f98]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_108,plain,
% 4.02/0.99      ( r1_tarski(sK3,sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2,plain,
% 4.02/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.02/0.99      inference(cnf_transformation,[],[f66]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_112,plain,
% 4.02/0.99      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2098,plain,
% 4.02/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 4.02/0.99      theory(equality) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2116,plain,
% 4.02/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2098]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_19,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.02/0.99      | v2_struct_0(X1)
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X1)
% 4.02/0.99      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2883,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,sK3)
% 4.02/0.99      | v2_struct_0(sK3)
% 4.02/0.99      | ~ l1_pre_topc(sK3)
% 4.02/0.99      | ~ v2_pre_topc(sK3)
% 4.02/0.99      | v1_funct_1(k4_tmap_1(sK3,X0)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2997,plain,
% 4.02/0.99      ( ~ m1_pre_topc(sK4,sK3)
% 4.02/0.99      | v2_struct_0(sK3)
% 4.02/0.99      | ~ l1_pre_topc(sK3)
% 4.02/0.99      | ~ v2_pre_topc(sK3)
% 4.02/0.99      | v1_funct_1(k4_tmap_1(sK3,sK4)) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2883]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2998,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v1_funct_1(k4_tmap_1(sK3,sK4)) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2997]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_18,plain,
% 4.02/0.99      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 4.02/0.99      | ~ m1_pre_topc(X1,X0)
% 4.02/0.99      | v2_struct_0(X0)
% 4.02/0.99      | ~ l1_pre_topc(X0)
% 4.02/0.99      | ~ v2_pre_topc(X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f80]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2870,plain,
% 4.02/0.99      ( v1_funct_2(k4_tmap_1(sK3,X0),u1_struct_0(X0),u1_struct_0(sK3))
% 4.02/0.99      | ~ m1_pre_topc(X0,sK3)
% 4.02/0.99      | v2_struct_0(sK3)
% 4.02/0.99      | ~ l1_pre_topc(sK3)
% 4.02/0.99      | ~ v2_pre_topc(sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3018,plain,
% 4.02/0.99      ( v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
% 4.02/0.99      | ~ m1_pre_topc(sK4,sK3)
% 4.02/0.99      | v2_struct_0(sK3)
% 4.02/0.99      | ~ l1_pre_topc(sK3)
% 4.02/0.99      | ~ v2_pre_topc(sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2870]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3019,plain,
% 4.02/0.99      ( v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3018]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2081,plain,( X0 = X0 ),theory(equality) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3505,plain,
% 4.02/0.99      ( sK5 = sK5 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2081]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6,plain,
% 4.02/0.99      ( r2_funct_2(X0,X1,X2,X2)
% 4.02/0.99      | ~ v1_funct_2(X2,X0,X1)
% 4.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/0.99      | ~ v1_funct_1(X2) ),
% 4.02/0.99      inference(cnf_transformation,[],[f101]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2751,plain,
% 4.02/0.99      ( r2_funct_2(X0,X1,X2,X2) = iProver_top
% 4.02/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3656,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5) = iProver_top
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2730,c_2751]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3657,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)
% 4.02/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
% 4.02/0.99      | ~ v1_funct_1(sK5) ),
% 4.02/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3656]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_21,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,X1)
% 4.02/0.99      | ~ m1_pre_topc(X2,X1)
% 4.02/0.99      | ~ m1_pre_topc(X0,X2)
% 4.02/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f84]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2738,plain,
% 4.02/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 4.02/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 4.02/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 4.02/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4047,plain,
% 4.02/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,X0) != iProver_top
% 4.02/0.99      | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2727,c_2738]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4103,plain,
% 4.02/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,X0) != iProver_top
% 4.02/0.99      | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) = iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_4047,c_38,c_39]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2754,plain,
% 4.02/0.99      ( X0 = X1
% 4.02/0.99      | r1_tarski(X0,X1) != iProver_top
% 4.02/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4109,plain,
% 4.02/0.99      ( u1_struct_0(X0) = u1_struct_0(sK4)
% 4.02/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,X0) != iProver_top
% 4.02/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_4103,c_2754]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4115,plain,
% 4.02/0.99      ( u1_struct_0(sK4) = u1_struct_0(sK4)
% 4.02/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2753,c_4109]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7,plain,
% 4.02/0.99      ( ~ r2_funct_2(X0,X1,X2,X3)
% 4.02/0.99      | ~ v1_funct_2(X2,X0,X1)
% 4.02/0.99      | ~ v1_funct_2(X3,X0,X1)
% 4.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/0.99      | ~ v1_funct_1(X2)
% 4.02/0.99      | ~ v1_funct_1(X3)
% 4.02/0.99      | X3 = X2 ),
% 4.02/0.99      inference(cnf_transformation,[],[f68]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2750,plain,
% 4.02/0.99      ( X0 = X1
% 4.02/0.99      | r2_funct_2(X2,X3,X1,X0) != iProver_top
% 4.02/0.99      | v1_funct_2(X1,X2,X3) != iProver_top
% 4.02/0.99      | v1_funct_2(X0,X2,X3) != iProver_top
% 4.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(X1) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4353,plain,
% 4.02/0.99      ( sK5 = X0
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) != iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2730,c_2750]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4441,plain,
% 4.02/0.99      ( v1_funct_1(X0) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | sK5 = X0
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) != iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_4353,c_42,c_43]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4442,plain,
% 4.02/0.99      ( sK5 = X0
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) != iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_4441]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4447,plain,
% 4.02/0.99      ( k4_tmap_1(sK3,sK4) = sK5
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) != iProver_top
% 4.02/0.99      | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2742,c_4442]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4724,plain,
% 4.02/0.99      ( k4_tmap_1(sK3,sK4) = sK5
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_4447,c_37,c_38,c_39,c_41,c_2998,c_3019]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2093,plain,
% 4.02/0.99      ( ~ r2_funct_2(X0,X1,X2,X3)
% 4.02/0.99      | r2_funct_2(X4,X5,X6,X7)
% 4.02/0.99      | X4 != X0
% 4.02/0.99      | X5 != X1
% 4.02/0.99      | X6 != X2
% 4.02/0.99      | X7 != X3 ),
% 4.02/0.99      theory(equality) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2802,plain,
% 4.02/0.99      ( ~ r2_funct_2(X0,X1,X2,X3)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
% 4.02/0.99      | k4_tmap_1(sK3,sK4) != X2
% 4.02/0.99      | u1_struct_0(sK3) != X1
% 4.02/0.99      | u1_struct_0(sK4) != X0
% 4.02/0.99      | sK5 != X3 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2093]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3075,plain,
% 4.02/0.99      ( ~ r2_funct_2(X0,X1,X2,sK5)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
% 4.02/0.99      | k4_tmap_1(sK3,sK4) != X2
% 4.02/0.99      | u1_struct_0(sK3) != X1
% 4.02/0.99      | u1_struct_0(sK4) != X0
% 4.02/0.99      | sK5 != sK5 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2802]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3989,plain,
% 4.02/0.99      ( ~ r2_funct_2(X0,u1_struct_0(sK3),X1,sK5)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
% 4.02/0.99      | k4_tmap_1(sK3,sK4) != X1
% 4.02/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 4.02/0.99      | u1_struct_0(sK4) != X0
% 4.02/0.99      | sK5 != sK5 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_3075]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5826,plain,
% 4.02/0.99      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X0,sK5)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
% 4.02/0.99      | k4_tmap_1(sK3,sK4) != X0
% 4.02/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 4.02/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 4.02/0.99      | sK5 != sK5 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_3989]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_9047,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
% 4.02/0.99      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)
% 4.02/0.99      | k4_tmap_1(sK3,sK4) != sK5
% 4.02/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 4.02/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 4.02/0.99      | sK5 != sK5 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_5826]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_9174,plain,
% 4.02/0.99      ( k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_8878,c_36,c_35,c_38,c_34,c_39,c_32,c_41,c_31,c_30,
% 4.02/0.99                 c_27,c_108,c_112,c_2116,c_2997,c_3018,c_3505,c_3509,
% 4.02/0.99                 c_3657,c_3829,c_4115,c_4449,c_8881,c_9047]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4530,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(X0,sK4,X1,X2,X3)) = k1_funct_1(sK5,sK2(X0,sK4,X1,X2,X3))
% 4.02/0.99      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK4,X0,X2,X1),X3) = iProver_top
% 4.02/0.99      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X1,sK4) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v2_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2734,c_4524]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4745,plain,
% 4.02/0.99      ( v2_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | m1_pre_topc(X1,sK4) != iProver_top
% 4.02/0.99      | v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK4,X0,X2,X1),X3) = iProver_top
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(X0,sK4,X1,X2,X3)) = k1_funct_1(sK5,sK2(X0,sK4,X1,X2,X3))
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_4530,c_38,c_39,c_40,c_41,c_2913,c_3009]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4746,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(X0,sK4,X1,X2,X3)) = k1_funct_1(sK5,sK2(X0,sK4,X1,X2,X3))
% 4.02/0.99      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK4,X0,X2,X1),X3) = iProver_top
% 4.02/0.99      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X1,sK4) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_4745]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5910,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,X0)) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0))
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_5902,c_4746]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6139,plain,
% 4.02/0.99      ( v1_funct_1(X0) != iProver_top
% 4.02/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,X0)) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0))
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_5910,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_3509,
% 4.02/0.99                 c_3829]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6140,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,X0)) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0))
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_6139]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6145,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)))
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top
% 4.02/0.99      | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2742,c_6140]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6399,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)))
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_6145,c_37,c_38,c_39,c_41,c_2998,c_3019]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6403,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)))
% 4.02/0.99      | k4_tmap_1(sK3,sK4) = sK5 ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_6399,c_4724]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_23,plain,
% 4.02/0.99      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 4.02/0.99      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 4.02/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 4.02/0.99      | ~ m1_pre_topc(X0,X2)
% 4.02/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 4.02/0.99      | v2_struct_0(X1)
% 4.02/0.99      | v2_struct_0(X2)
% 4.02/0.99      | v2_struct_0(X0)
% 4.02/0.99      | ~ l1_pre_topc(X1)
% 4.02/0.99      | ~ l1_pre_topc(X2)
% 4.02/0.99      | ~ v2_pre_topc(X1)
% 4.02/0.99      | ~ v2_pre_topc(X2)
% 4.02/0.99      | ~ v1_funct_1(X3)
% 4.02/0.99      | ~ v1_funct_1(X4)
% 4.02/0.99      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK2(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK2(X1,X2,X0,X3,X4)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f87]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2736,plain,
% 4.02/0.99      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X1,X0,X3,X2,X4)) != k1_funct_1(X4,sK2(X1,X0,X3,X2,X4))
% 4.02/0.99      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X0,X1,X2,X3),X4) = iProver_top
% 4.02/0.99      | v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) != iProver_top
% 4.02/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(X3) = iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_pre_topc(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(X2) != iProver_top
% 4.02/0.99      | v1_funct_1(X4) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6534,plain,
% 4.02/0.99      ( k4_tmap_1(sK3,sK4) = sK5
% 4.02/0.99      | k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) != k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)))
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK4,sK3,sK5,sK4),k4_tmap_1(sK3,sK4)) = iProver_top
% 4.02/0.99      | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top
% 4.02/0.99      | m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_6403,c_2736]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6535,plain,
% 4.02/0.99      ( k4_tmap_1(sK3,sK4) = sK5
% 4.02/0.99      | k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) != k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)))
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top
% 4.02/0.99      | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top
% 4.02/0.99      | m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(light_normalisation,[status(thm)],[c_6534,c_5902]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2881,plain,
% 4.02/0.99      ( ~ m1_pre_topc(X0,sK3)
% 4.02/0.99      | m1_subset_1(k4_tmap_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 4.02/0.99      | v2_struct_0(sK3)
% 4.02/0.99      | ~ l1_pre_topc(sK3)
% 4.02/0.99      | ~ v2_pre_topc(sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3023,plain,
% 4.02/0.99      ( ~ m1_pre_topc(sK4,sK3)
% 4.02/0.99      | m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 4.02/0.99      | v2_struct_0(sK3)
% 4.02/0.99      | ~ l1_pre_topc(sK3)
% 4.02/0.99      | ~ v2_pre_topc(sK3) ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_2881]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3024,plain,
% 4.02/0.99      ( m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3023]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8544,plain,
% 4.02/0.99      ( k4_tmap_1(sK3,sK4) = sK5
% 4.02/0.99      | k1_funct_1(k4_tmap_1(sK3,sK4),sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) != k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_6535,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_2913,
% 4.02/0.99                 c_2998,c_3009,c_3019,c_3024,c_3509,c_3829,c_4447]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_9176,plain,
% 4.02/0.99      ( k4_tmap_1(sK3,sK4) = sK5
% 4.02/0.99      | k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) != sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)) ),
% 4.02/0.99      inference(demodulation,[status(thm)],[c_9174,c_8544]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_28,negated_conjecture,
% 4.02/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 4.02/0.99      | ~ r2_hidden(X0,u1_struct_0(sK4))
% 4.02/0.99      | k1_funct_1(sK5,X0) = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f97]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2731,plain,
% 4.02/0.99      ( k1_funct_1(sK5,X0) = X0
% 4.02/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6542,plain,
% 4.02/0.99      ( k1_funct_1(sK5,sK2(X0,X1,X2,X3,X4)) = sK2(X0,X1,X2,X3,X4)
% 4.02/0.99      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) = iProver_top
% 4.02/0.99      | v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 4.02/0.99      | m1_pre_topc(X1,sK3) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(sK4)) != iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v2_struct_0(X2) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X4) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_4240,c_2731]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6763,plain,
% 4.02/0.99      ( l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | k1_funct_1(sK5,sK2(X0,X1,X2,X3,X4)) = sK2(X0,X1,X2,X3,X4)
% 4.02/0.99      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) = iProver_top
% 4.02/0.99      | v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 4.02/0.99      | m1_pre_topc(X1,sK3) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(sK4)) != iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v2_struct_0(X2) = iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X4) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_6542,c_37,c_39]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6764,plain,
% 4.02/0.99      ( k1_funct_1(sK5,sK2(X0,X1,X2,X3,X4)) = sK2(X0,X1,X2,X3,X4)
% 4.02/0.99      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) = iProver_top
% 4.02/0.99      | v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 4.02/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 4.02/0.99      | m1_pre_topc(X1,sK3) != iProver_top
% 4.02/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 4.02/0.99      | r2_hidden(sK2(X0,X1,X2,X3,X4),u1_struct_0(sK4)) != iProver_top
% 4.02/0.99      | v2_struct_0(X1) = iProver_top
% 4.02/0.99      | v2_struct_0(X0) = iProver_top
% 4.02/0.99      | v2_struct_0(X2) = iProver_top
% 4.02/0.99      | l1_pre_topc(X1) != iProver_top
% 4.02/0.99      | l1_pre_topc(X0) != iProver_top
% 4.02/0.99      | v2_pre_topc(X1) != iProver_top
% 4.02/0.99      | v2_pre_topc(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(X3) != iProver_top
% 4.02/0.99      | v1_funct_1(X4) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_6763]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6767,plain,
% 4.02/0.99      ( k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK4) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | r2_hidden(sK2(sK3,sK4,sK4,sK5,X0),u1_struct_0(sK4)) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | v2_struct_0(sK4) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | l1_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK4) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top
% 4.02/0.99      | v1_funct_1(sK5) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_5902,c_6764]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6982,plain,
% 4.02/0.99      ( v1_funct_1(X0) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_6767,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_2913,
% 4.02/0.99                 c_3009,c_3509,c_3829,c_5908]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6983,plain,
% 4.02/0.99      ( k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,X0)) = sK2(sK3,sK4,sK4,sK5,X0)
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = iProver_top
% 4.02/0.99      | v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 4.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 4.02/0.99      inference(renaming,[status(thm)],[c_6982]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6988,plain,
% 4.02/0.99      ( k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top
% 4.02/0.99      | v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 4.02/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 4.02/0.99      | v2_struct_0(sK3) = iProver_top
% 4.02/0.99      | l1_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v2_pre_topc(sK3) != iProver_top
% 4.02/0.99      | v1_funct_1(k4_tmap_1(sK3,sK4)) != iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_2742,c_6983]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7206,plain,
% 4.02/0.99      ( k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))
% 4.02/0.99      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) = iProver_top ),
% 4.02/0.99      inference(global_propositional_subsumption,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_6988,c_37,c_38,c_39,c_41,c_2998,c_3019]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7210,plain,
% 4.02/0.99      ( k4_tmap_1(sK3,sK4) = sK5
% 4.02/0.99      | k1_funct_1(sK5,sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4))) = sK2(sK3,sK4,sK4,sK5,k4_tmap_1(sK3,sK4)) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_7206,c_4724]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(contradiction,plain,
% 4.02/0.99      ( $false ),
% 4.02/0.99      inference(minisat,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_9176,c_9047,c_7210,c_4115,c_3829,c_3657,c_3509,c_3505,
% 4.02/0.99                 c_2116,c_112,c_108,c_27,c_30,c_31,c_41,c_39,c_38]) ).
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  ------                               Statistics
% 4.02/0.99  
% 4.02/0.99  ------ General
% 4.02/0.99  
% 4.02/0.99  abstr_ref_over_cycles:                  0
% 4.02/0.99  abstr_ref_under_cycles:                 0
% 4.02/0.99  gc_basic_clause_elim:                   0
% 4.02/0.99  forced_gc_time:                         0
% 4.02/0.99  parsing_time:                           0.012
% 4.02/0.99  unif_index_cands_time:                  0.
% 4.02/0.99  unif_index_add_time:                    0.
% 4.02/0.99  orderings_time:                         0.
% 4.02/0.99  out_proof_time:                         0.024
% 4.02/0.99  total_time:                             0.454
% 4.02/0.99  num_of_symbols:                         57
% 4.02/0.99  num_of_terms:                           11548
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing
% 4.02/0.99  
% 4.02/0.99  num_of_splits:                          0
% 4.02/0.99  num_of_split_atoms:                     0
% 4.02/0.99  num_of_reused_defs:                     0
% 4.02/0.99  num_eq_ax_congr_red:                    52
% 4.02/0.99  num_of_sem_filtered_clauses:            1
% 4.02/0.99  num_of_subtypes:                        0
% 4.02/0.99  monotx_restored_types:                  0
% 4.02/0.99  sat_num_of_epr_types:                   0
% 4.02/0.99  sat_num_of_non_cyclic_types:            0
% 4.02/0.99  sat_guarded_non_collapsed_types:        0
% 4.02/0.99  num_pure_diseq_elim:                    0
% 4.02/0.99  simp_replaced_by:                       0
% 4.02/0.99  res_preprocessed:                       182
% 4.02/0.99  prep_upred:                             0
% 4.02/0.99  prep_unflattend:                        76
% 4.02/0.99  smt_new_axioms:                         0
% 4.02/0.99  pred_elim_cands:                        11
% 4.02/0.99  pred_elim:                              1
% 4.02/0.99  pred_elim_cl:                           1
% 4.02/0.99  pred_elim_cycles:                       5
% 4.02/0.99  merged_defs:                            0
% 4.02/0.99  merged_defs_ncl:                        0
% 4.02/0.99  bin_hyper_res:                          0
% 4.02/0.99  prep_cycles:                            4
% 4.02/0.99  pred_elim_time:                         0.051
% 4.02/0.99  splitting_time:                         0.
% 4.02/0.99  sem_filter_time:                        0.
% 4.02/0.99  monotx_time:                            0.001
% 4.02/0.99  subtype_inf_time:                       0.
% 4.02/0.99  
% 4.02/0.99  ------ Problem properties
% 4.02/0.99  
% 4.02/0.99  clauses:                                35
% 4.02/0.99  conjectures:                            10
% 4.02/0.99  epr:                                    11
% 4.02/0.99  horn:                                   21
% 4.02/0.99  ground:                                 9
% 4.02/0.99  unary:                                  10
% 4.02/0.99  binary:                                 2
% 4.02/0.99  lits:                                   187
% 4.02/0.99  lits_eq:                                11
% 4.02/0.99  fd_pure:                                0
% 4.02/0.99  fd_pseudo:                              0
% 4.02/0.99  fd_cond:                                0
% 4.02/0.99  fd_pseudo_cond:                         5
% 4.02/0.99  ac_symbols:                             0
% 4.02/0.99  
% 4.02/0.99  ------ Propositional Solver
% 4.02/0.99  
% 4.02/0.99  prop_solver_calls:                      31
% 4.02/0.99  prop_fast_solver_calls:                 3873
% 4.02/0.99  smt_solver_calls:                       0
% 4.02/0.99  smt_fast_solver_calls:                  0
% 4.02/0.99  prop_num_of_clauses:                    3099
% 4.02/0.99  prop_preprocess_simplified:             10675
% 4.02/0.99  prop_fo_subsumed:                       267
% 4.02/0.99  prop_solver_time:                       0.
% 4.02/0.99  smt_solver_time:                        0.
% 4.02/0.99  smt_fast_solver_time:                   0.
% 4.02/0.99  prop_fast_solver_time:                  0.
% 4.02/0.99  prop_unsat_core_time:                   0.
% 4.02/0.99  
% 4.02/0.99  ------ QBF
% 4.02/0.99  
% 4.02/0.99  qbf_q_res:                              0
% 4.02/0.99  qbf_num_tautologies:                    0
% 4.02/0.99  qbf_prep_cycles:                        0
% 4.02/0.99  
% 4.02/0.99  ------ BMC1
% 4.02/0.99  
% 4.02/0.99  bmc1_current_bound:                     -1
% 4.02/0.99  bmc1_last_solved_bound:                 -1
% 4.02/0.99  bmc1_unsat_core_size:                   -1
% 4.02/0.99  bmc1_unsat_core_parents_size:           -1
% 4.02/0.99  bmc1_merge_next_fun:                    0
% 4.02/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation
% 4.02/0.99  
% 4.02/0.99  inst_num_of_clauses:                    875
% 4.02/0.99  inst_num_in_passive:                    192
% 4.02/0.99  inst_num_in_active:                     606
% 4.02/0.99  inst_num_in_unprocessed:                77
% 4.02/0.99  inst_num_of_loops:                      670
% 4.02/0.99  inst_num_of_learning_restarts:          0
% 4.02/0.99  inst_num_moves_active_passive:          61
% 4.02/0.99  inst_lit_activity:                      0
% 4.02/0.99  inst_lit_activity_moves:                0
% 4.02/0.99  inst_num_tautologies:                   0
% 4.02/0.99  inst_num_prop_implied:                  0
% 4.02/0.99  inst_num_existing_simplified:           0
% 4.02/0.99  inst_num_eq_res_simplified:             0
% 4.02/0.99  inst_num_child_elim:                    0
% 4.02/0.99  inst_num_of_dismatching_blockings:      552
% 4.02/0.99  inst_num_of_non_proper_insts:           1412
% 4.02/0.99  inst_num_of_duplicates:                 0
% 4.02/0.99  inst_inst_num_from_inst_to_res:         0
% 4.02/0.99  inst_dismatching_checking_time:         0.
% 4.02/0.99  
% 4.02/0.99  ------ Resolution
% 4.02/0.99  
% 4.02/0.99  res_num_of_clauses:                     0
% 4.02/0.99  res_num_in_passive:                     0
% 4.02/0.99  res_num_in_active:                      0
% 4.02/0.99  res_num_of_loops:                       186
% 4.02/0.99  res_forward_subset_subsumed:            64
% 4.02/0.99  res_backward_subset_subsumed:           0
% 4.02/0.99  res_forward_subsumed:                   0
% 4.02/0.99  res_backward_subsumed:                  0
% 4.02/0.99  res_forward_subsumption_resolution:     0
% 4.02/0.99  res_backward_subsumption_resolution:    0
% 4.02/0.99  res_clause_to_clause_subsumption:       864
% 4.02/0.99  res_orphan_elimination:                 0
% 4.02/0.99  res_tautology_del:                      93
% 4.02/0.99  res_num_eq_res_simplified:              0
% 4.02/0.99  res_num_sel_changes:                    0
% 4.02/0.99  res_moves_from_active_to_pass:          0
% 4.02/0.99  
% 4.02/0.99  ------ Superposition
% 4.02/0.99  
% 4.02/0.99  sup_time_total:                         0.
% 4.02/0.99  sup_time_generating:                    0.
% 4.02/0.99  sup_time_sim_full:                      0.
% 4.02/0.99  sup_time_sim_immed:                     0.
% 4.02/0.99  
% 4.02/0.99  sup_num_of_clauses:                     147
% 4.02/0.99  sup_num_in_active:                      118
% 4.02/0.99  sup_num_in_passive:                     29
% 4.02/0.99  sup_num_of_loops:                       133
% 4.02/0.99  sup_fw_superposition:                   87
% 4.02/0.99  sup_bw_superposition:                   63
% 4.02/0.99  sup_immediate_simplified:               24
% 4.02/0.99  sup_given_eliminated:                   0
% 4.02/0.99  comparisons_done:                       0
% 4.02/0.99  comparisons_avoided:                    110
% 4.02/0.99  
% 4.02/0.99  ------ Simplifications
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  sim_fw_subset_subsumed:                 7
% 4.02/0.99  sim_bw_subset_subsumed:                 7
% 4.02/0.99  sim_fw_subsumed:                        7
% 4.02/0.99  sim_bw_subsumed:                        5
% 4.02/0.99  sim_fw_subsumption_res:                 0
% 4.02/0.99  sim_bw_subsumption_res:                 0
% 4.02/0.99  sim_tautology_del:                      6
% 4.02/0.99  sim_eq_tautology_del:                   4
% 4.02/0.99  sim_eq_res_simp:                        0
% 4.02/0.99  sim_fw_demodulated:                     6
% 4.02/0.99  sim_bw_demodulated:                     4
% 4.02/0.99  sim_light_normalised:                   3
% 4.02/0.99  sim_joinable_taut:                      0
% 4.02/0.99  sim_joinable_simp:                      0
% 4.02/0.99  sim_ac_normalised:                      0
% 4.02/0.99  sim_smt_subsumption:                    0
% 4.02/0.99  
%------------------------------------------------------------------------------
