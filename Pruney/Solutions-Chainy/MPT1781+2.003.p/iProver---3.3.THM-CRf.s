%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:43 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_7178)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f55,f54,f53])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f51,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
                        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
                        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f51])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
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

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f7,axiom,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1060,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1729,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1060])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1073,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_struct_0(X2_52)
    | ~ l1_struct_0(X1_52)
    | ~ l1_struct_0(X0_52)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1716,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | l1_struct_0(X2_52) != iProver_top
    | l1_struct_0(X1_52) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1073])).

cnf(c_3643,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_52)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1716])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_90,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_92,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1079,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1057,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2364,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_1079,c_1057])).

cnf(c_2365,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2364])).

cnf(c_1080,plain,
    ( l1_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2501,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_2502,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2501])).

cnf(c_3684,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_52)) = iProver_top
    | l1_struct_0(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3643,c_35,c_38,c_39,c_92,c_2365,c_2502])).

cnf(c_3685,plain,
    ( l1_struct_0(X0_52) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_52)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3684])).

cnf(c_19,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1066,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53)
    | ~ v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | m1_subset_1(sK0(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X2_52))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1723,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53) = iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(sK0(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X2_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1066])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1084,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X1_53,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X0_54)
    | k3_funct_2(X0_54,X1_54,X0_53,X1_53) = k1_funct_1(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1705,plain,
    ( k3_funct_2(X0_54,X1_54,X0_53,X1_53) = k1_funct_1(X0_53,X1_53)
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X1_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1084])).

cnf(c_3022,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = k1_funct_1(sK3,X0_53)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1705])).

cnf(c_3523,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = k1_funct_1(sK3,X0_53)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3022,c_38,c_39])).

cnf(c_3524,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = k1_funct_1(sK3,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3523])).

cnf(c_6104,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53))
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_53,X1_52),X1_53) = iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_3524])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_37,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1081,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2538,plain,
    ( ~ m1_pre_topc(sK2,X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_2539,plain,
    ( m1_pre_topc(sK2,X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2538])).

cnf(c_2541,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2539])).

cnf(c_6816,plain,
    ( v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_53,X1_52),X1_53) = iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53))
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6104,c_34,c_35,c_36,c_37,c_2365,c_2541])).

cnf(c_6817,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53))
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_53,X1_52),X1_53) = iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6816])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1075,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | m1_subset_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | ~ l1_struct_0(X2_52)
    | ~ l1_struct_0(X1_52)
    | ~ l1_struct_0(X0_52)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1714,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) = iProver_top
    | l1_struct_0(X2_52) != iProver_top
    | l1_struct_0(X1_52) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1075])).

cnf(c_3,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1082,plain,
    ( ~ r2_funct_2(X0_54,X1_54,X0_53,X1_53)
    | ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ v1_funct_2(X1_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | X1_53 = X0_53 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1707,plain,
    ( X0_53 = X1_53
    | r2_funct_2(X0_54,X1_54,X1_53,X0_53) != iProver_top
    | v1_funct_2(X1_53,X0_54,X1_54) != iProver_top
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1082])).

cnf(c_3859,plain,
    ( sK3 = X0_53
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,sK3) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1707])).

cnf(c_4040,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | sK3 = X0_53
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,sK3) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3859,c_38,c_39])).

cnf(c_4041,plain,
    ( sK3 = X0_53
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,sK3) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4040])).

cnf(c_4063,plain,
    ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X0_52,sK1,X0_53,sK2),sK3) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_52,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_4041])).

cnf(c_5208,plain,
    ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X0_52,sK1,X0_53,sK2),sK3) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_52,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4063,c_35,c_92,c_2365,c_2502])).

cnf(c_6836,plain,
    ( k2_tmap_1(sK2,sK1,X0_53,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_53,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_53,sK3))
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,X0_53,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6817,c_5208])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1069,plain,
    ( m1_pre_topc(X0_52,X0_52)
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2557,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_2562,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2557])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1074,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | v1_funct_2(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_struct_0(X2_52)
    | ~ l1_struct_0(X1_52)
    | ~ l1_struct_0(X0_52)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2392,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(sK2,sK1,X0_53,X0_52),u1_struct_0(X0_52),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_52)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_7087,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
    | v1_funct_2(k2_tmap_1(sK2,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_7088,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7087])).

cnf(c_7175,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,X0_53,sK2)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k2_tmap_1(sK2,sK1,X0_53,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_53,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_53,sK3))
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6836,c_33,c_34,c_35,c_36,c_38,c_39,c_40,c_92,c_2365,c_2502,c_2562,c_7088])).

cnf(c_7176,plain,
    ( k2_tmap_1(sK2,sK1,X0_53,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_53,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_53,sK3))
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,X0_53,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7175])).

cnf(c_7188,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_7176])).

cnf(c_1715,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),u1_struct_0(X2_52),u1_struct_0(X1_52)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | l1_struct_0(X2_52) != iProver_top
    | l1_struct_0(X1_52) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1074])).

cnf(c_18,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1067,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53)
    | ~ v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | r2_hidden(sK0(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X0_52))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1722,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53) = iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | r2_hidden(sK0(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_5222,plain,
    ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_52,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1722,c_5208])).

cnf(c_1116,plain,
    ( l1_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1080])).

cnf(c_5339,plain,
    ( v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_52,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5222,c_33,c_34,c_35,c_36,c_38,c_39,c_40,c_1116])).

cnf(c_5340,plain,
    ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_52,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5339])).

cnf(c_5356,plain,
    ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1715,c_5340])).

cnf(c_5361,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
    | k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5356,c_35,c_92,c_1116,c_2365,c_2502])).

cnf(c_5362,plain,
    ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5361])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1085,plain,
    ( ~ r2_hidden(X0_53,X0_54)
    | ~ v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1704,plain,
    ( r2_hidden(X0_53,X0_54) != iProver_top
    | v1_xboole_0(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_5377,plain,
    ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5362,c_1704])).

cnf(c_5548,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_5377])).

cnf(c_5633,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5548,c_34,c_35,c_36,c_37,c_38,c_39,c_2365,c_2541,c_2562])).

cnf(c_5634,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5633])).

cnf(c_5640,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3685,c_5634])).

cnf(c_5788,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5640,c_35,c_2365,c_2502])).

cnf(c_7253,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
    | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7188,c_35,c_38,c_39,c_40,c_2365,c_2502,c_5640,c_7178])).

cnf(c_7254,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7253])).

cnf(c_7260,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
    | l1_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3685,c_7254])).

cnf(c_7261,plain,
    ( ~ l1_struct_0(sK2)
    | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7260])).

cnf(c_7426,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
    | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7260,c_35,c_2365,c_2502])).

cnf(c_7427,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3)) ),
    inference(renaming,[status(thm)],[c_7426])).

cnf(c_17,plain,
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
    | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1068,plain,
    ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53)
    | ~ v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | k3_funct_2(u1_struct_0(X2_52),u1_struct_0(X1_52),X0_53,sK0(X1_52,X2_52,X0_52,X0_53,X1_53)) != k1_funct_1(X1_53,sK0(X1_52,X2_52,X0_52,X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1721,plain,
    ( k3_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,sK0(X1_52,X0_52,X2_52,X0_53,X1_53)) != k1_funct_1(X1_53,sK0(X1_52,X0_52,X2_52,X0_53,X1_53))
    | r2_funct_2(u1_struct_0(X2_52),u1_struct_0(X1_52),k2_tmap_1(X0_52,X1_52,X0_53,X2_52),X1_53) = iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_7430,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7427,c_1721])).

cnf(c_7433,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7430,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_2365,c_2541,c_2562])).

cnf(c_7439,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7433,c_5208])).

cnf(c_2270,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,X0_52),u1_struct_0(X0_52),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_52)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_5712,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2270])).

cnf(c_5713,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5712])).

cnf(c_8755,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7439,c_35,c_38,c_39,c_40,c_92,c_2365,c_2502,c_5713])).

cnf(c_8756,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8755])).

cnf(c_8761,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | l1_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3685,c_8756])).

cnf(c_9271,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8761,c_35,c_2365,c_2502])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1072,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1717,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1072])).

cnf(c_3860,plain,
    ( k4_tmap_1(X0_52,X1_52) = X0_53
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_1707])).

cnf(c_14,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1071,plain,
    ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52))
    | ~ m1_pre_topc(X1_52,X0_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1135,plain,
    ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) = iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1071])).

cnf(c_9961,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
    | k4_tmap_1(X0_52,X1_52) = X0_53
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3860,c_1135])).

cnf(c_9962,plain,
    ( k4_tmap_1(X0_52,X1_52) = X0_53
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9961])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1070,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | v1_funct_1(k4_tmap_1(X1_52,X0_52)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1719,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_52,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1070])).

cnf(c_9977,plain,
    ( k4_tmap_1(X0_52,X1_52) = X0_53
    | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9962,c_1719])).

cnf(c_9985,plain,
    ( k2_tmap_1(sK2,X0_52,X0_53,X1_52) = k4_tmap_1(X0_52,X1_52)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52)))
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_53,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52)) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6817,c_9977])).

cnf(c_23,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1087,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_1104,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_2,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1083,plain,
    ( r2_funct_2(X0_54,X1_54,X0_53,X0_53)
    | ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2232,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_1095,plain,
    ( ~ r2_funct_2(X0_54,X1_54,X0_53,X1_53)
    | r2_funct_2(X0_54,X1_54,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_2380,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,X1_53)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | X0_53 != sK3
    | X1_53 != sK3 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_2571,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | k4_tmap_1(sK1,sK2) != sK3
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2380])).

cnf(c_6938,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_6939,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6938])).

cnf(c_3285,plain,
    ( v1_funct_2(k4_tmap_1(sK1,X0_52),u1_struct_0(X0_52),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_52,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_7892,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3285])).

cnf(c_7895,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7892])).

cnf(c_4400,plain,
    ( ~ m1_pre_topc(X0_52,sK1)
    | m1_subset_1(k4_tmap_1(sK1,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_9267,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4400])).

cnf(c_9268,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9267])).

cnf(c_9276,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9271,c_1722])).

cnf(c_13554,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9276,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_2365,c_2541,c_2562])).

cnf(c_13555,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_13554])).

cnf(c_13563,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13555,c_1704])).

cnf(c_14398,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_13563])).

cnf(c_2574,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,X1_53)
    | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | X1_53 = X0_53 ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_3738,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,k4_tmap_1(X0_52,X1_52))
    | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k4_tmap_1(X0_52,X1_52))
    | k4_tmap_1(X0_52,X1_52) = X0_53 ),
    inference(instantiation,[status(thm)],[c_2574])).

cnf(c_14579,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = X0_53 ),
    inference(instantiation,[status(thm)],[c_3738])).

cnf(c_14581,plain,
    ( k4_tmap_1(sK1,sK2) = X0_53
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14579])).

cnf(c_14583,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14581])).

cnf(c_15891,plain,
    ( v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | k2_tmap_1(sK2,X0_52,X0_53,X1_52) = k4_tmap_1(X0_52,X1_52)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52)))
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_53,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9985,c_33,c_34,c_35,c_37,c_27,c_38,c_26,c_39,c_25,c_40,c_23,c_1104,c_1135,c_2232,c_2571,c_6939,c_7895,c_9268,c_14398,c_14583])).

cnf(c_15892,plain,
    ( k2_tmap_1(sK2,X0_52,X0_53,X1_52) = k4_tmap_1(X0_52,X1_52)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52)))
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_53,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52)) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15891])).

cnf(c_15913,plain,
    ( k2_tmap_1(sK2,X0_52,X0_53,X1_52) = k4_tmap_1(X0_52,X1_52)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52)))
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_53,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15892,c_1719,c_1717])).

cnf(c_15918,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = k4_tmap_1(sK1,sK2)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9271,c_15913])).

cnf(c_9275,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9271,c_1723])).

cnf(c_9871,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9275,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_2365,c_2541,c_2562])).

cnf(c_9872,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_9871])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1078,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | m1_subset_1(X0_53,u1_struct_0(X1_52))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1711,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_9882,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_9872,c_1711])).

cnf(c_10446,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9882,c_36])).

cnf(c_10447,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_10446])).

cnf(c_24,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1061,negated_conjecture,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ r2_hidden(X0_53,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1728,plain,
    ( k1_funct_1(sK3,X0_53) = X0_53
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1061])).

cnf(c_10458,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_10447,c_1728])).

cnf(c_10817,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10458,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_2365,c_2541,c_2562,c_9276])).

cnf(c_10818,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_10817])).

cnf(c_10827,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_10818])).

cnf(c_11058,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10827,c_33,c_34,c_35,c_37,c_6939,c_7895])).

cnf(c_11064,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11058,c_9977])).

cnf(c_11602,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11064,c_33,c_34,c_35,c_37,c_27,c_38,c_26,c_39,c_25,c_40,c_23,c_1104,c_2232,c_2571])).

cnf(c_15932,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15918,c_9271,c_11602])).

cnf(c_9883,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_53)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_53))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9872,c_3524])).

cnf(c_11011,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_9883])).

cnf(c_12877,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11011,c_33,c_34,c_35,c_37,c_6939,c_7895])).

cnf(c_12881,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12877,c_11602])).

cnf(c_12885,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12881])).

cnf(c_14436,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14398])).

cnf(c_14582,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | k4_tmap_1(sK1,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_14579])).

cnf(c_16236,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15932,c_32,c_31,c_30,c_28,c_27,c_26,c_25,c_23,c_1104,c_2232,c_2571,c_6938,c_7892,c_9267,c_12885,c_14436,c_14582])).

cnf(c_16239,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_16236,c_1721])).

cnf(c_1732,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_10461,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X1_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_10447,c_1711])).

cnf(c_1117,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_11875,plain,
    ( v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X1_52)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10461,c_1117])).

cnf(c_11876,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK2,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X1_52)) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_11875])).

cnf(c_11889,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK1)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_11876])).

cnf(c_11911,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11889,c_33,c_35,c_36,c_2365,c_2562])).

cnf(c_11912,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_11911])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1063,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X1_52))
    | ~ r2_hidden(X0_53,u1_struct_0(X0_52))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | k1_funct_1(k4_tmap_1(X1_52,X0_52),X0_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1726,plain,
    ( k1_funct_1(k4_tmap_1(X0_52,X1_52),X0_53) = X0_53
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | r2_hidden(X0_53,u1_struct_0(X1_52)) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_11922,plain,
    ( k1_funct_1(k4_tmap_1(sK1,X0_52),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_11912,c_1726])).

cnf(c_12696,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | k1_funct_1(k4_tmap_1(sK1,X0_52),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11922,c_33,c_34,c_35])).

cnf(c_12697,plain,
    ( k1_funct_1(k4_tmap_1(sK1,X0_52),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_12696])).

cnf(c_13564,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_13555,c_12697])).

cnf(c_13616,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13564,c_36,c_37])).

cnf(c_13617,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_13616])).

cnf(c_13626,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_13617])).

cnf(c_13664,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13626])).

cnf(c_14888,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13626,c_32,c_31,c_30,c_28,c_27,c_26,c_25,c_23,c_1104,c_2232,c_2571,c_6938,c_7892,c_9267,c_13664,c_14582])).

cnf(c_16240,plain,
    ( sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16239,c_9271,c_14888])).

cnf(c_16241,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_16240])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16241,c_14583,c_9268,c_7895,c_6939,c_2571,c_2562,c_2541,c_2365,c_2232,c_1104,c_23,c_40,c_25,c_39,c_26,c_38,c_27,c_37,c_36,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.53/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.53/1.49  
% 7.53/1.49  ------  iProver source info
% 7.53/1.49  
% 7.53/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.53/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.53/1.49  git: non_committed_changes: false
% 7.53/1.49  git: last_make_outside_of_git: false
% 7.53/1.49  
% 7.53/1.49  ------ 
% 7.53/1.49  ------ Parsing...
% 7.53/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.53/1.49  
% 7.53/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.53/1.49  ------ Proving...
% 7.53/1.49  ------ Problem Properties 
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  clauses                                 33
% 7.53/1.49  conjectures                             10
% 7.53/1.49  EPR                                     12
% 7.53/1.49  Horn                                    21
% 7.53/1.49  unary                                   9
% 7.53/1.49  binary                                  3
% 7.53/1.49  lits                                    182
% 7.53/1.49  lits eq                                 7
% 7.53/1.49  fd_pure                                 0
% 7.53/1.49  fd_pseudo                               0
% 7.53/1.49  fd_cond                                 0
% 7.53/1.49  fd_pseudo_cond                          1
% 7.53/1.49  AC symbols                              0
% 7.53/1.49  
% 7.53/1.49  ------ Input Options Time Limit: Unbounded
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  ------ 
% 7.53/1.49  Current options:
% 7.53/1.49  ------ 
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  ------ Proving...
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  % SZS status Theorem for theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  fof(f17,conjecture,(
% 7.53/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f18,negated_conjecture,(
% 7.53/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.53/1.49    inference(negated_conjecture,[],[f17])).
% 7.53/1.49  
% 7.53/1.49  fof(f48,plain,(
% 7.53/1.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f18])).
% 7.53/1.49  
% 7.53/1.49  fof(f49,plain,(
% 7.53/1.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.53/1.49    inference(flattening,[],[f48])).
% 7.53/1.49  
% 7.53/1.49  fof(f55,plain,(
% 7.53/1.49    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.53/1.49    introduced(choice_axiom,[])).
% 7.53/1.49  
% 7.53/1.49  fof(f54,plain,(
% 7.53/1.49    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.53/1.49    introduced(choice_axiom,[])).
% 7.53/1.49  
% 7.53/1.49  fof(f53,plain,(
% 7.53/1.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 7.53/1.49    introduced(choice_axiom,[])).
% 7.53/1.49  
% 7.53/1.49  fof(f56,plain,(
% 7.53/1.49    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 7.53/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f55,f54,f53])).
% 7.53/1.49  
% 7.53/1.49  fof(f87,plain,(
% 7.53/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 7.53/1.49    inference(cnf_transformation,[],[f56])).
% 7.53/1.49  
% 7.53/1.49  fof(f10,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f35,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f10])).
% 7.53/1.49  
% 7.53/1.49  fof(f36,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 7.53/1.49    inference(flattening,[],[f35])).
% 7.53/1.49  
% 7.53/1.49  fof(f67,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f36])).
% 7.53/1.49  
% 7.53/1.49  fof(f82,plain,(
% 7.53/1.49    l1_pre_topc(sK1)),
% 7.53/1.49    inference(cnf_transformation,[],[f56])).
% 7.53/1.49  
% 7.53/1.49  fof(f85,plain,(
% 7.53/1.49    v1_funct_1(sK3)),
% 7.53/1.49    inference(cnf_transformation,[],[f56])).
% 7.53/1.49  
% 7.53/1.49  fof(f86,plain,(
% 7.53/1.49    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 7.53/1.49    inference(cnf_transformation,[],[f56])).
% 7.53/1.49  
% 7.53/1.49  fof(f5,axiom,(
% 7.53/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f27,plain,(
% 7.53/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.53/1.49    inference(ennf_transformation,[],[f5])).
% 7.53/1.49  
% 7.53/1.49  fof(f62,plain,(
% 7.53/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f27])).
% 7.53/1.49  
% 7.53/1.49  fof(f6,axiom,(
% 7.53/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f28,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.53/1.49    inference(ennf_transformation,[],[f6])).
% 7.53/1.49  
% 7.53/1.49  fof(f63,plain,(
% 7.53/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f28])).
% 7.53/1.49  
% 7.53/1.49  fof(f84,plain,(
% 7.53/1.49    m1_pre_topc(sK2,sK1)),
% 7.53/1.49    inference(cnf_transformation,[],[f56])).
% 7.53/1.49  
% 7.53/1.49  fof(f13,axiom,(
% 7.53/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f40,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f13])).
% 7.53/1.49  
% 7.53/1.49  fof(f41,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.49    inference(flattening,[],[f40])).
% 7.53/1.49  
% 7.53/1.49  fof(f51,plain,(
% 7.53/1.49    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 7.53/1.49    introduced(choice_axiom,[])).
% 7.53/1.49  
% 7.53/1.49  fof(f52,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f51])).
% 7.53/1.49  
% 7.53/1.49  fof(f74,plain,(
% 7.53/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f52])).
% 7.53/1.49  
% 7.53/1.49  fof(f2,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f21,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f2])).
% 7.53/1.49  
% 7.53/1.49  fof(f22,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.53/1.49    inference(flattening,[],[f21])).
% 7.53/1.49  
% 7.53/1.49  fof(f58,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f22])).
% 7.53/1.49  
% 7.53/1.49  fof(f81,plain,(
% 7.53/1.49    v2_pre_topc(sK1)),
% 7.53/1.49    inference(cnf_transformation,[],[f56])).
% 7.53/1.49  
% 7.53/1.49  fof(f83,plain,(
% 7.53/1.49    ~v2_struct_0(sK2)),
% 7.53/1.49    inference(cnf_transformation,[],[f56])).
% 7.53/1.49  
% 7.53/1.49  fof(f4,axiom,(
% 7.53/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f25,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f4])).
% 7.53/1.49  
% 7.53/1.49  fof(f26,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.53/1.49    inference(flattening,[],[f25])).
% 7.53/1.49  
% 7.53/1.49  fof(f61,plain,(
% 7.53/1.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f26])).
% 7.53/1.49  
% 7.53/1.49  fof(f69,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f36])).
% 7.53/1.49  
% 7.53/1.49  fof(f3,axiom,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f23,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.53/1.49    inference(ennf_transformation,[],[f3])).
% 7.53/1.49  
% 7.53/1.49  fof(f24,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.53/1.49    inference(flattening,[],[f23])).
% 7.53/1.49  
% 7.53/1.49  fof(f50,plain,(
% 7.53/1.49    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.53/1.49    inference(nnf_transformation,[],[f24])).
% 7.53/1.49  
% 7.53/1.49  fof(f59,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f50])).
% 7.53/1.49  
% 7.53/1.49  fof(f80,plain,(
% 7.53/1.49    ~v2_struct_0(sK1)),
% 7.53/1.49    inference(cnf_transformation,[],[f56])).
% 7.53/1.49  
% 7.53/1.49  fof(f12,axiom,(
% 7.53/1.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f39,plain,(
% 7.53/1.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.53/1.49    inference(ennf_transformation,[],[f12])).
% 7.53/1.49  
% 7.53/1.49  fof(f73,plain,(
% 7.53/1.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f39])).
% 7.53/1.49  
% 7.53/1.49  fof(f68,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f36])).
% 7.53/1.49  
% 7.53/1.49  fof(f75,plain,(
% 7.53/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f52])).
% 7.53/1.49  
% 7.53/1.49  fof(f1,axiom,(
% 7.53/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f19,plain,(
% 7.53/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 7.53/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 7.53/1.49  
% 7.53/1.49  fof(f20,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 7.53/1.49    inference(ennf_transformation,[],[f19])).
% 7.53/1.49  
% 7.53/1.49  fof(f57,plain,(
% 7.53/1.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f20])).
% 7.53/1.49  
% 7.53/1.49  fof(f76,plain,(
% 7.53/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f52])).
% 7.53/1.49  
% 7.53/1.49  fof(f11,axiom,(
% 7.53/1.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f37,plain,(
% 7.53/1.49    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f11])).
% 7.53/1.49  
% 7.53/1.49  fof(f38,plain,(
% 7.53/1.49    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.49    inference(flattening,[],[f37])).
% 7.53/1.49  
% 7.53/1.49  fof(f72,plain,(
% 7.53/1.49    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f38])).
% 7.53/1.49  
% 7.53/1.49  fof(f71,plain,(
% 7.53/1.49    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f38])).
% 7.53/1.49  
% 7.53/1.49  fof(f70,plain,(
% 7.53/1.49    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f38])).
% 7.53/1.49  
% 7.53/1.49  fof(f89,plain,(
% 7.53/1.49    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 7.53/1.49    inference(cnf_transformation,[],[f56])).
% 7.53/1.49  
% 7.53/1.49  fof(f60,plain,(
% 7.53/1.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f50])).
% 7.53/1.49  
% 7.53/1.49  fof(f90,plain,(
% 7.53/1.49    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.53/1.49    inference(equality_resolution,[],[f60])).
% 7.53/1.49  
% 7.53/1.49  fof(f7,axiom,(
% 7.53/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f29,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f7])).
% 7.53/1.49  
% 7.53/1.49  fof(f30,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.49    inference(flattening,[],[f29])).
% 7.53/1.49  
% 7.53/1.49  fof(f64,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f30])).
% 7.53/1.49  
% 7.53/1.49  fof(f88,plain,(
% 7.53/1.49    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 7.53/1.49    inference(cnf_transformation,[],[f56])).
% 7.53/1.49  
% 7.53/1.49  fof(f16,axiom,(
% 7.53/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 7.53/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.53/1.49  
% 7.53/1.49  fof(f46,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.53/1.49    inference(ennf_transformation,[],[f16])).
% 7.53/1.49  
% 7.53/1.49  fof(f47,plain,(
% 7.53/1.49    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.53/1.49    inference(flattening,[],[f46])).
% 7.53/1.49  
% 7.53/1.49  fof(f79,plain,(
% 7.53/1.49    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.53/1.49    inference(cnf_transformation,[],[f47])).
% 7.53/1.49  
% 7.53/1.49  cnf(c_25,negated_conjecture,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.53/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1060,negated_conjecture,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1729,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1060]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_12,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.53/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.53/1.49      | ~ l1_struct_0(X3)
% 7.53/1.49      | ~ l1_struct_0(X2)
% 7.53/1.49      | ~ l1_struct_0(X1)
% 7.53/1.49      | ~ v1_funct_1(X0)
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 7.53/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1073,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.53/1.49      | ~ l1_struct_0(X2_52)
% 7.53/1.49      | ~ l1_struct_0(X1_52)
% 7.53/1.49      | ~ l1_struct_0(X0_52)
% 7.53/1.49      | ~ v1_funct_1(X0_53)
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52)) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1716,plain,
% 7.53/1.49      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.53/1.49      | l1_struct_0(X2_52) != iProver_top
% 7.53/1.49      | l1_struct_0(X1_52) != iProver_top
% 7.53/1.49      | l1_struct_0(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52)) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1073]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3643,plain,
% 7.53/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | l1_struct_0(X0_52) != iProver_top
% 7.53/1.49      | l1_struct_0(sK1) != iProver_top
% 7.53/1.49      | l1_struct_0(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_52)) = iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1729,c_1716]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_30,negated_conjecture,
% 7.53/1.49      ( l1_pre_topc(sK1) ),
% 7.53/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_35,plain,
% 7.53/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_27,negated_conjecture,
% 7.53/1.49      ( v1_funct_1(sK3) ),
% 7.53/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_38,plain,
% 7.53/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_26,negated_conjecture,
% 7.53/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 7.53/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_39,plain,
% 7.53/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5,plain,
% 7.53/1.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_90,plain,
% 7.53/1.49      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_92,plain,
% 7.53/1.49      ( l1_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_90]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1079,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.53/1.49      | ~ l1_pre_topc(X1_52)
% 7.53/1.49      | l1_pre_topc(X0_52) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_28,negated_conjecture,
% 7.53/1.49      ( m1_pre_topc(sK2,sK1) ),
% 7.53/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1057,negated_conjecture,
% 7.53/1.49      ( m1_pre_topc(sK2,sK1) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_28]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2364,plain,
% 7.53/1.49      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK2) ),
% 7.53/1.49      inference(resolution,[status(thm)],[c_1079,c_1057]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2365,plain,
% 7.53/1.49      ( l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_2364]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1080,plain,
% 7.53/1.49      ( l1_struct_0(X0_52) | ~ l1_pre_topc(X0_52) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2501,plain,
% 7.53/1.49      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1080]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2502,plain,
% 7.53/1.49      ( l1_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_2501]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3684,plain,
% 7.53/1.49      ( v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_52)) = iProver_top
% 7.53/1.49      | l1_struct_0(X0_52) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_3643,c_35,c_38,c_39,c_92,c_2365,c_2502]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3685,plain,
% 7.53/1.49      ( l1_struct_0(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_52)) = iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_3684]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_19,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.53/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.53/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.53/1.49      | ~ m1_pre_topc(X0,X2)
% 7.53/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.53/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.53/1.49      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 7.53/1.49      | v2_struct_0(X1)
% 7.53/1.49      | v2_struct_0(X2)
% 7.53/1.49      | v2_struct_0(X0)
% 7.53/1.49      | ~ l1_pre_topc(X1)
% 7.53/1.49      | ~ l1_pre_topc(X2)
% 7.53/1.49      | ~ v2_pre_topc(X1)
% 7.53/1.49      | ~ v2_pre_topc(X2)
% 7.53/1.49      | ~ v1_funct_1(X3)
% 7.53/1.49      | ~ v1_funct_1(X4) ),
% 7.53/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1066,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53)
% 7.53/1.49      | ~ v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.53/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 7.53/1.49      | ~ m1_pre_topc(X0_52,X2_52)
% 7.53/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 7.53/1.49      | m1_subset_1(sK0(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X2_52))
% 7.53/1.49      | v2_struct_0(X1_52)
% 7.53/1.49      | v2_struct_0(X0_52)
% 7.53/1.49      | v2_struct_0(X2_52)
% 7.53/1.49      | ~ l1_pre_topc(X1_52)
% 7.53/1.49      | ~ l1_pre_topc(X2_52)
% 7.53/1.49      | ~ v2_pre_topc(X1_52)
% 7.53/1.49      | ~ v2_pre_topc(X2_52)
% 7.53/1.49      | ~ v1_funct_1(X0_53)
% 7.53/1.49      | ~ v1_funct_1(X1_53) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1723,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK0(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X2_52)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X2_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(X2_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X2_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(X1_53) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1066]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.53/1.49      | ~ m1_subset_1(X3,X1)
% 7.53/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.53/1.49      | ~ v1_funct_1(X0)
% 7.53/1.49      | v1_xboole_0(X1)
% 7.53/1.49      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.53/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1084,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 7.53/1.49      | ~ m1_subset_1(X1_53,X0_54)
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.53/1.49      | ~ v1_funct_1(X0_53)
% 7.53/1.49      | v1_xboole_0(X0_54)
% 7.53/1.49      | k3_funct_2(X0_54,X1_54,X0_53,X1_53) = k1_funct_1(X0_53,X1_53) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1705,plain,
% 7.53/1.49      ( k3_funct_2(X0_54,X1_54,X0_53,X1_53) = k1_funct_1(X0_53,X1_53)
% 7.53/1.49      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 7.53/1.49      | m1_subset_1(X1_53,X0_54) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1084]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3022,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = k1_funct_1(sK3,X0_53)
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1729,c_1705]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3523,plain,
% 7.53/1.49      ( m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = k1_funct_1(sK3,X0_53)
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_3022,c_38,c_39]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3524,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = k1_funct_1(sK3,X0_53)
% 7.53/1.49      | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_3523]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6104,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53))
% 7.53/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_53,X1_52),X1_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X1_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1723,c_3524]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_31,negated_conjecture,
% 7.53/1.49      ( v2_pre_topc(sK1) ),
% 7.53/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_34,plain,
% 7.53/1.49      ( v2_pre_topc(sK1) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_29,negated_conjecture,
% 7.53/1.49      ( ~ v2_struct_0(sK2) ),
% 7.53/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_36,plain,
% 7.53/1.49      ( v2_struct_0(sK2) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_37,plain,
% 7.53/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.53/1.49      | ~ l1_pre_topc(X1)
% 7.53/1.49      | ~ v2_pre_topc(X1)
% 7.53/1.49      | v2_pre_topc(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1081,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.53/1.49      | ~ l1_pre_topc(X1_52)
% 7.53/1.49      | ~ v2_pre_topc(X1_52)
% 7.53/1.49      | v2_pre_topc(X0_52) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2538,plain,
% 7.53/1.49      ( ~ m1_pre_topc(sK2,X0_52)
% 7.53/1.49      | ~ l1_pre_topc(X0_52)
% 7.53/1.49      | ~ v2_pre_topc(X0_52)
% 7.53/1.49      | v2_pre_topc(sK2) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1081]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2539,plain,
% 7.53/1.49      ( m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK2) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_2538]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2541,plain,
% 7.53/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK2) = iProver_top ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_2539]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6816,plain,
% 7.53/1.49      ( v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(X1_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_53,X1_52),X1_53) = iProver_top
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53))
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_6104,c_34,c_35,c_36,c_37,c_2365,c_2541]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6817,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53)) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,X1_53))
% 7.53/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK2,X0_52,X0_53,X1_52),X1_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X1_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_6816]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.53/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.53/1.49      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.53/1.49      | ~ l1_struct_0(X3)
% 7.53/1.49      | ~ l1_struct_0(X2)
% 7.53/1.49      | ~ l1_struct_0(X1)
% 7.53/1.49      | ~ v1_funct_1(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1075,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.53/1.49      | m1_subset_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 7.53/1.49      | ~ l1_struct_0(X2_52)
% 7.53/1.49      | ~ l1_struct_0(X1_52)
% 7.53/1.49      | ~ l1_struct_0(X0_52)
% 7.53/1.49      | ~ v1_funct_1(X0_53) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1714,plain,
% 7.53/1.49      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) = iProver_top
% 7.53/1.49      | l1_struct_0(X2_52) != iProver_top
% 7.53/1.49      | l1_struct_0(X1_52) != iProver_top
% 7.53/1.49      | l1_struct_0(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1075]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3,plain,
% 7.53/1.49      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.53/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.53/1.49      | ~ v1_funct_2(X3,X0,X1)
% 7.53/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.53/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.53/1.49      | ~ v1_funct_1(X2)
% 7.53/1.49      | ~ v1_funct_1(X3)
% 7.53/1.49      | X3 = X2 ),
% 7.53/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1082,plain,
% 7.53/1.49      ( ~ r2_funct_2(X0_54,X1_54,X0_53,X1_53)
% 7.53/1.49      | ~ v1_funct_2(X0_53,X0_54,X1_54)
% 7.53/1.49      | ~ v1_funct_2(X1_53,X0_54,X1_54)
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.53/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.53/1.49      | ~ v1_funct_1(X0_53)
% 7.53/1.49      | ~ v1_funct_1(X1_53)
% 7.53/1.49      | X1_53 = X0_53 ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1707,plain,
% 7.53/1.49      ( X0_53 = X1_53
% 7.53/1.49      | r2_funct_2(X0_54,X1_54,X1_53,X0_53) != iProver_top
% 7.53/1.49      | v1_funct_2(X1_53,X0_54,X1_54) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 7.53/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.53/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1082]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3859,plain,
% 7.53/1.49      ( sK3 = X0_53
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,sK3) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1729,c_1707]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4040,plain,
% 7.53/1.49      ( v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | sK3 = X0_53
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,sK3) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_3859,c_38,c_39]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4041,plain,
% 7.53/1.49      ( sK3 = X0_53
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,sK3) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_4040]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4063,plain,
% 7.53/1.49      ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X0_52,sK1,X0_53,sK2),sK3) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(X0_52,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | l1_struct_0(X0_52) != iProver_top
% 7.53/1.49      | l1_struct_0(sK1) != iProver_top
% 7.53/1.49      | l1_struct_0(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1714,c_4041]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5208,plain,
% 7.53/1.49      ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(X0_52,sK1,X0_53,sK2),sK3) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(X0_52,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | l1_struct_0(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_4063,c_35,c_92,c_2365,c_2502]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6836,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_53,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_53,sK3))
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_struct_0(sK2) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,X0_53,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_6817,c_5208]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_32,negated_conjecture,
% 7.53/1.49      ( ~ v2_struct_0(sK1) ),
% 7.53/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_33,plain,
% 7.53/1.49      ( v2_struct_0(sK1) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_40,plain,
% 7.53/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_16,plain,
% 7.53/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1069,plain,
% 7.53/1.49      ( m1_pre_topc(X0_52,X0_52) | ~ l1_pre_topc(X0_52) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2557,plain,
% 7.53/1.49      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1069]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2562,plain,
% 7.53/1.49      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_2557]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.53/1.49      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 7.53/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.53/1.49      | ~ l1_struct_0(X3)
% 7.53/1.49      | ~ l1_struct_0(X2)
% 7.53/1.49      | ~ l1_struct_0(X1)
% 7.53/1.49      | ~ v1_funct_1(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1074,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.53/1.49      | v1_funct_2(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),u1_struct_0(X2_52),u1_struct_0(X1_52))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.53/1.49      | ~ l1_struct_0(X2_52)
% 7.53/1.49      | ~ l1_struct_0(X1_52)
% 7.53/1.49      | ~ l1_struct_0(X0_52)
% 7.53/1.49      | ~ v1_funct_1(X0_53) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2392,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,X0_53,X0_52),u1_struct_0(X0_52),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ l1_struct_0(X0_52)
% 7.53/1.49      | ~ l1_struct_0(sK1)
% 7.53/1.49      | ~ l1_struct_0(sK2)
% 7.53/1.49      | ~ v1_funct_1(X0_53) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1074]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7087,plain,
% 7.53/1.49      ( ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ l1_struct_0(sK1)
% 7.53/1.49      | ~ l1_struct_0(sK2)
% 7.53/1.49      | ~ v1_funct_1(X0_53) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_2392]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7088,plain,
% 7.53/1.49      ( v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | l1_struct_0(sK1) != iProver_top
% 7.53/1.49      | l1_struct_0(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_7087]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7175,plain,
% 7.53/1.49      ( v1_funct_1(k2_tmap_1(sK2,sK1,X0_53,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | k2_tmap_1(sK2,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_53,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_53,sK3))
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_6836,c_33,c_34,c_35,c_36,c_38,c_39,c_40,c_92,c_2365,
% 7.53/1.49                 c_2502,c_2562,c_7088]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7176,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_53,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_53,sK3))
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,X0_53,sK2)) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_7175]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7188,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1729,c_7176]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1715,plain,
% 7.53/1.49      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(X0_52,X1_52,X0_53,X2_52),u1_struct_0(X2_52),u1_struct_0(X1_52)) = iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.53/1.49      | l1_struct_0(X2_52) != iProver_top
% 7.53/1.49      | l1_struct_0(X1_52) != iProver_top
% 7.53/1.49      | l1_struct_0(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1074]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_18,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.53/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.53/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.53/1.49      | ~ m1_pre_topc(X0,X2)
% 7.53/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.53/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.53/1.49      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 7.53/1.49      | v2_struct_0(X1)
% 7.53/1.49      | v2_struct_0(X2)
% 7.53/1.49      | v2_struct_0(X0)
% 7.53/1.49      | ~ l1_pre_topc(X1)
% 7.53/1.49      | ~ l1_pre_topc(X2)
% 7.53/1.49      | ~ v2_pre_topc(X1)
% 7.53/1.49      | ~ v2_pre_topc(X2)
% 7.53/1.49      | ~ v1_funct_1(X3)
% 7.53/1.49      | ~ v1_funct_1(X4) ),
% 7.53/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1067,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53)
% 7.53/1.49      | ~ v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.53/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 7.53/1.49      | ~ m1_pre_topc(X0_52,X2_52)
% 7.53/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 7.53/1.49      | r2_hidden(sK0(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X0_52))
% 7.53/1.49      | v2_struct_0(X1_52)
% 7.53/1.49      | v2_struct_0(X0_52)
% 7.53/1.49      | v2_struct_0(X2_52)
% 7.53/1.49      | ~ l1_pre_topc(X1_52)
% 7.53/1.49      | ~ l1_pre_topc(X2_52)
% 7.53/1.49      | ~ v2_pre_topc(X1_52)
% 7.53/1.49      | ~ v2_pre_topc(X2_52)
% 7.53/1.49      | ~ v1_funct_1(X0_53)
% 7.53/1.49      | ~ v1_funct_1(X1_53) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1722,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(X1_52,X2_52,X0_52,X0_53,X1_53),u1_struct_0(X0_52)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X2_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(X2_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X2_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(X1_53) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5222,plain,
% 7.53/1.49      ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(X0_52,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_struct_0(X0_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1722,c_5208]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1116,plain,
% 7.53/1.49      ( l1_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1080]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5339,plain,
% 7.53/1.49      ( v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(X0_52,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_5222,c_33,c_34,c_35,c_36,c_38,c_39,c_40,c_1116]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5340,plain,
% 7.53/1.49      ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(X0_52,sK1,X0_53,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_5339]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5356,plain,
% 7.53/1.49      ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_struct_0(X0_52) != iProver_top
% 7.53/1.49      | l1_struct_0(sK1) != iProver_top
% 7.53/1.49      | l1_struct_0(sK2) != iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1715,c_5340]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5361,plain,
% 7.53/1.49      ( v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_5356,c_35,c_92,c_1116,c_2365,c_2502]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5362,plain,
% 7.53/1.49      ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,X0_52,sK2,X0_53,sK3),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_5361]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_0,plain,
% 7.53/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.53/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1085,plain,
% 7.53/1.49      ( ~ r2_hidden(X0_53,X0_54) | ~ v1_xboole_0(X0_54) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1704,plain,
% 7.53/1.49      ( r2_hidden(X0_53,X0_54) != iProver_top
% 7.53/1.49      | v1_xboole_0(X0_54) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5377,plain,
% 7.53/1.49      ( k2_tmap_1(X0_52,sK1,X0_53,sK2) = sK3
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(X0_52,sK1,X0_53,sK2)) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_5362,c_1704]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5548,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1729,c_5377]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5633,plain,
% 7.53/1.49      ( v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.53/1.49      | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_5548,c_34,c_35,c_36,c_37,c_38,c_39,c_2365,c_2541,
% 7.53/1.49                 c_2562]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5634,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_5633]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5640,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | l1_struct_0(sK2) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_3685,c_5634]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5788,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_5640,c_35,c_2365,c_2502]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7253,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
% 7.53/1.49      | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_7188,c_35,c_38,c_39,c_40,c_2365,c_2502,c_5640,c_7178]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7254,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_7253]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7260,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
% 7.53/1.49      | l1_struct_0(sK2) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_3685,c_7254]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7261,plain,
% 7.53/1.49      ( ~ l1_struct_0(sK2)
% 7.53/1.49      | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3)) ),
% 7.53/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_7260]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7426,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
% 7.53/1.49      | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_7260,c_35,c_2365,c_2502]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7427,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3)) ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_7426]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_17,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.53/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.53/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.53/1.49      | ~ m1_pre_topc(X0,X2)
% 7.53/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.53/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.53/1.49      | v2_struct_0(X1)
% 7.53/1.49      | v2_struct_0(X2)
% 7.53/1.49      | v2_struct_0(X0)
% 7.53/1.49      | ~ l1_pre_topc(X1)
% 7.53/1.49      | ~ l1_pre_topc(X2)
% 7.53/1.49      | ~ v2_pre_topc(X1)
% 7.53/1.49      | ~ v2_pre_topc(X2)
% 7.53/1.49      | ~ v1_funct_1(X3)
% 7.53/1.49      | ~ v1_funct_1(X4)
% 7.53/1.49      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
% 7.53/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1068,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),k2_tmap_1(X2_52,X1_52,X0_53,X0_52),X1_53)
% 7.53/1.49      | ~ v1_funct_2(X1_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 7.53/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 7.53/1.49      | ~ m1_pre_topc(X0_52,X2_52)
% 7.53/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 7.53/1.49      | v2_struct_0(X1_52)
% 7.53/1.49      | v2_struct_0(X0_52)
% 7.53/1.49      | v2_struct_0(X2_52)
% 7.53/1.49      | ~ l1_pre_topc(X1_52)
% 7.53/1.49      | ~ l1_pre_topc(X2_52)
% 7.53/1.49      | ~ v2_pre_topc(X1_52)
% 7.53/1.49      | ~ v2_pre_topc(X2_52)
% 7.53/1.49      | ~ v1_funct_1(X0_53)
% 7.53/1.49      | ~ v1_funct_1(X1_53)
% 7.53/1.49      | k3_funct_2(u1_struct_0(X2_52),u1_struct_0(X1_52),X0_53,sK0(X1_52,X2_52,X0_52,X0_53,X1_53)) != k1_funct_1(X1_53,sK0(X1_52,X2_52,X0_52,X0_53,X1_53)) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1721,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,sK0(X1_52,X0_52,X2_52,X0_53,X1_53)) != k1_funct_1(X1_53,sK0(X1_52,X0_52,X2_52,X0_53,X1_53))
% 7.53/1.49      | r2_funct_2(u1_struct_0(X2_52),u1_struct_0(X1_52),k2_tmap_1(X0_52,X1_52,X0_53,X2_52),X1_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X2_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(X1_53) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1068]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7430,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) = iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_7427,c_1721]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7433,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_7430,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_2365,
% 7.53/1.49                 c_2541,c_2562]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7439,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | l1_struct_0(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_7433,c_5208]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2270,plain,
% 7.53/1.49      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,X0_52),u1_struct_0(X0_52),u1_struct_0(sK1))
% 7.53/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ l1_struct_0(X0_52)
% 7.53/1.49      | ~ l1_struct_0(sK1)
% 7.53/1.49      | ~ l1_struct_0(sK2)
% 7.53/1.49      | ~ v1_funct_1(sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1074]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5712,plain,
% 7.53/1.49      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ l1_struct_0(sK1)
% 7.53/1.49      | ~ l1_struct_0(sK2)
% 7.53/1.49      | ~ v1_funct_1(sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_2270]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_5713,plain,
% 7.53/1.49      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | l1_struct_0(sK1) != iProver_top
% 7.53/1.49      | l1_struct_0(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_5712]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8755,plain,
% 7.53/1.49      ( v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.53/1.49      | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_7439,c_35,c_38,c_39,c_40,c_92,c_2365,c_2502,c_5713]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8756,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_8755]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_8761,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.53/1.49      | l1_struct_0(sK2) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_3685,c_8756]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9271,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_8761,c_35,c_2365,c_2502]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_13,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.53/1.49      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.53/1.49      | v2_struct_0(X1)
% 7.53/1.49      | ~ l1_pre_topc(X1)
% 7.53/1.49      | ~ v2_pre_topc(X1) ),
% 7.53/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1072,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.53/1.49      | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 7.53/1.49      | v2_struct_0(X1_52)
% 7.53/1.49      | ~ l1_pre_topc(X1_52)
% 7.53/1.49      | ~ v2_pre_topc(X1_52) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1717,plain,
% 7.53/1.49      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.53/1.49      | m1_subset_1(k4_tmap_1(X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X1_52) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1072]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3860,plain,
% 7.53/1.49      ( k4_tmap_1(X0_52,X1_52) = X0_53
% 7.53/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1717,c_1707]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_14,plain,
% 7.53/1.49      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.53/1.49      | ~ m1_pre_topc(X1,X0)
% 7.53/1.49      | v2_struct_0(X0)
% 7.53/1.49      | ~ l1_pre_topc(X0)
% 7.53/1.49      | ~ v2_pre_topc(X0) ),
% 7.53/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1071,plain,
% 7.53/1.49      ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52))
% 7.53/1.49      | ~ m1_pre_topc(X1_52,X0_52)
% 7.53/1.49      | v2_struct_0(X0_52)
% 7.53/1.49      | ~ l1_pre_topc(X0_52)
% 7.53/1.49      | ~ v2_pre_topc(X0_52) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1135,plain,
% 7.53/1.49      ( v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) = iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1071]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9961,plain,
% 7.53/1.49      ( v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
% 7.53/1.49      | k4_tmap_1(X0_52,X1_52) = X0_53
% 7.53/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_3860,c_1135]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9962,plain,
% 7.53/1.49      ( k4_tmap_1(X0_52,X1_52) = X0_53
% 7.53/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_9961]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_15,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.53/1.49      | v2_struct_0(X1)
% 7.53/1.49      | ~ l1_pre_topc(X1)
% 7.53/1.49      | ~ v2_pre_topc(X1)
% 7.53/1.49      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 7.53/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1070,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.53/1.49      | v2_struct_0(X1_52)
% 7.53/1.49      | ~ l1_pre_topc(X1_52)
% 7.53/1.49      | ~ v2_pre_topc(X1_52)
% 7.53/1.49      | v1_funct_1(k4_tmap_1(X1_52,X0_52)) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1719,plain,
% 7.53/1.49      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(X1_52,X0_52)) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1070]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9977,plain,
% 7.53/1.49      ( k4_tmap_1(X0_52,X1_52) = X0_53
% 7.53/1.49      | r2_funct_2(u1_struct_0(X1_52),u1_struct_0(X0_52),X0_53,k4_tmap_1(X0_52,X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(forward_subsumption_resolution,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_9962,c_1719]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9985,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,X0_52,X0_53,X1_52) = k4_tmap_1(X0_52,X1_52)
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52)))
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_53,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_6817,c_9977]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_23,negated_conjecture,
% 7.53/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 7.53/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1087,plain,( X0_53 = X0_53 ),theory(equality) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1104,plain,
% 7.53/1.49      ( sK3 = sK3 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1087]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2,plain,
% 7.53/1.49      ( r2_funct_2(X0,X1,X2,X2)
% 7.53/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.53/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.53/1.49      | ~ v1_funct_1(X2) ),
% 7.53/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1083,plain,
% 7.53/1.49      ( r2_funct_2(X0_54,X1_54,X0_53,X0_53)
% 7.53/1.49      | ~ v1_funct_2(X0_53,X0_54,X1_54)
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.53/1.49      | ~ v1_funct_1(X0_53) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2232,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 7.53/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ v1_funct_1(sK3) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1083]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1095,plain,
% 7.53/1.49      ( ~ r2_funct_2(X0_54,X1_54,X0_53,X1_53)
% 7.53/1.49      | r2_funct_2(X0_54,X1_54,X2_53,X3_53)
% 7.53/1.49      | X2_53 != X0_53
% 7.53/1.49      | X3_53 != X1_53 ),
% 7.53/1.49      theory(equality) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2380,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,X1_53)
% 7.53/1.49      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 7.53/1.49      | X0_53 != sK3
% 7.53/1.49      | X1_53 != sK3 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1095]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2571,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 7.53/1.49      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 7.53/1.49      | k4_tmap_1(sK1,sK2) != sK3
% 7.53/1.49      | sK3 != sK3 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_2380]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6938,plain,
% 7.53/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 7.53/1.49      | v2_struct_0(sK1)
% 7.53/1.49      | ~ l1_pre_topc(sK1)
% 7.53/1.49      | ~ v2_pre_topc(sK1)
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1070]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_6939,plain,
% 7.53/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_6938]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3285,plain,
% 7.53/1.49      ( v1_funct_2(k4_tmap_1(sK1,X0_52),u1_struct_0(X0_52),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_pre_topc(X0_52,sK1)
% 7.53/1.49      | v2_struct_0(sK1)
% 7.53/1.49      | ~ l1_pre_topc(sK1)
% 7.53/1.49      | ~ v2_pre_topc(sK1) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1071]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7892,plain,
% 7.53/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_pre_topc(sK2,sK1)
% 7.53/1.49      | v2_struct_0(sK1)
% 7.53/1.49      | ~ l1_pre_topc(sK1)
% 7.53/1.49      | ~ v2_pre_topc(sK1) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_3285]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7895,plain,
% 7.53/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_7892]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_4400,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0_52,sK1)
% 7.53/1.49      | m1_subset_1(k4_tmap_1(sK1,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
% 7.53/1.49      | v2_struct_0(sK1)
% 7.53/1.49      | ~ l1_pre_topc(sK1)
% 7.53/1.49      | ~ v2_pre_topc(sK1) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1072]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9267,plain,
% 7.53/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 7.53/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | v2_struct_0(sK1)
% 7.53/1.49      | ~ l1_pre_topc(sK1)
% 7.53/1.49      | ~ v2_pre_topc(sK1) ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_4400]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9268,plain,
% 7.53/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_9267]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9276,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_9271,c_1722]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_13554,plain,
% 7.53/1.49      ( v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_9276,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_2365,
% 7.53/1.49                 c_2541,c_2562]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_13555,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_13554]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_13563,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_13555,c_1704]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_14398,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1717,c_13563]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_2574,plain,
% 7.53/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,X1_53)
% 7.53/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ v1_funct_1(X0_53)
% 7.53/1.49      | ~ v1_funct_1(X1_53)
% 7.53/1.49      | X1_53 = X0_53 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_1082]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_3738,plain,
% 7.53/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,k4_tmap_1(X0_52,X1_52))
% 7.53/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ v1_funct_2(k4_tmap_1(X0_52,X1_52),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ v1_funct_1(X0_53)
% 7.53/1.49      | ~ v1_funct_1(k4_tmap_1(X0_52,X1_52))
% 7.53/1.49      | k4_tmap_1(X0_52,X1_52) = X0_53 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_2574]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_14579,plain,
% 7.53/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ v1_funct_1(X0_53)
% 7.53/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.53/1.49      | k4_tmap_1(sK1,sK2) = X0_53 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_3738]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_14581,plain,
% 7.53/1.49      ( k4_tmap_1(sK1,sK2) = X0_53
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_14579]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_14583,plain,
% 7.53/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_14581]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_15891,plain,
% 7.53/1.49      ( v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.53/1.49      | k2_tmap_1(sK2,X0_52,X0_53,X1_52) = k4_tmap_1(X0_52,X1_52)
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52)))
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_53,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_9985,c_33,c_34,c_35,c_37,c_27,c_38,c_26,c_39,c_25,
% 7.53/1.49                 c_40,c_23,c_1104,c_1135,c_2232,c_2571,c_6939,c_7895,
% 7.53/1.49                 c_9268,c_14398,c_14583]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_15892,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,X0_52,X0_53,X1_52) = k4_tmap_1(X0_52,X1_52)
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52)))
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_53,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(k4_tmap_1(X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52)) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(X0_52,X1_52)) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_15891]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_15913,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,X0_52,X0_53,X1_52) = k4_tmap_1(X0_52,X1_52)
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52))) = k1_funct_1(sK3,sK0(X0_52,sK2,X1_52,X0_53,k4_tmap_1(X0_52,X1_52)))
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v1_funct_2(k2_tmap_1(sK2,X0_52,X0_53,X1_52),u1_struct_0(X1_52),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.53/1.49      | m1_pre_topc(X1_52,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | m1_subset_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,X0_52,X0_53,X1_52)) != iProver_top ),
% 7.53/1.49      inference(forward_subsumption_resolution,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_15892,c_1719,c_1717]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_15918,plain,
% 7.53/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = k4_tmap_1(sK1,sK2)
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.53/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_9271,c_15913]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9275,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_9271,c_1723]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9871,plain,
% 7.53/1.49      ( v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_9275,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_2365,
% 7.53/1.49                 c_2541,c_2562]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9872,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) = iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_9871]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_7,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.53/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.53/1.49      | m1_subset_1(X2,u1_struct_0(X1))
% 7.53/1.49      | v2_struct_0(X1)
% 7.53/1.49      | v2_struct_0(X0)
% 7.53/1.49      | ~ l1_pre_topc(X1) ),
% 7.53/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1078,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.53/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 7.53/1.49      | m1_subset_1(X0_53,u1_struct_0(X1_52))
% 7.53/1.49      | v2_struct_0(X1_52)
% 7.53/1.49      | v2_struct_0(X0_52)
% 7.53/1.49      | ~ l1_pre_topc(X1_52) ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1711,plain,
% 7.53/1.49      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,u1_struct_0(X1_52)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X1_52) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1078]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9882,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_9872,c_1711]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10446,plain,
% 7.53/1.49      ( v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) = iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_9882,c_36]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10447,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_10446]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_24,negated_conjecture,
% 7.53/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.53/1.49      | ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.53/1.49      | k1_funct_1(sK3,X0) = X0 ),
% 7.53/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1061,negated_conjecture,
% 7.53/1.49      ( ~ m1_subset_1(X0_53,u1_struct_0(sK1))
% 7.53/1.49      | ~ r2_hidden(X0_53,u1_struct_0(sK2))
% 7.53/1.49      | k1_funct_1(sK3,X0_53) = X0_53 ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_24]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1728,plain,
% 7.53/1.49      ( k1_funct_1(sK3,X0_53) = X0_53
% 7.53/1.49      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | r2_hidden(X0_53,u1_struct_0(sK2)) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1061]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10458,plain,
% 7.53/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK2)) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_10447,c_1728]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10817,plain,
% 7.53/1.49      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_10458,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_2365,
% 7.53/1.49                 c_2541,c_2562,c_9276]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10818,plain,
% 7.53/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_10817]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10827,plain,
% 7.53/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1717,c_10818]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11058,plain,
% 7.53/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_10827,c_33,c_34,c_35,c_37,c_6939,c_7895]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11064,plain,
% 7.53/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.53/1.49      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_11058,c_9977]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11602,plain,
% 7.53/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_11064,c_33,c_34,c_35,c_37,c_27,c_38,c_26,c_39,c_25,
% 7.53/1.49                 c_40,c_23,c_1104,c_2232,c_2571]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_15932,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | k4_tmap_1(sK1,sK2) = sK3
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(light_normalisation,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_15918,c_9271,c_11602]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_9883,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_53)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_53))
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_9872,c_3524]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11011,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1717,c_9883]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_12877,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_11011,c_33,c_34,c_35,c_37,c_6939,c_7895]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_12881,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.53/1.49      inference(light_normalisation,[status(thm)],[c_12877,c_11602]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_12885,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | v1_xboole_0(u1_struct_0(sK2))
% 7.53/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.53/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_12881]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_14436,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_pre_topc(sK2,sK1)
% 7.53/1.49      | v2_struct_0(sK1)
% 7.53/1.49      | ~ l1_pre_topc(sK1)
% 7.53/1.49      | ~ v2_pre_topc(sK1)
% 7.53/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.53/1.49      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 7.53/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_14398]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_14582,plain,
% 7.53/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.53/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.53/1.49      | ~ v1_funct_1(sK3)
% 7.53/1.49      | k4_tmap_1(sK1,sK2) = sK3 ),
% 7.53/1.49      inference(instantiation,[status(thm)],[c_14579]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_16236,plain,
% 7.53/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_15932,c_32,c_31,c_30,c_28,c_27,c_26,c_25,c_23,c_1104,
% 7.53/1.49                 c_2232,c_2571,c_6938,c_7892,c_9267,c_12885,c_14436,
% 7.53/1.49                 c_14582]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_16239,plain,
% 7.53/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_16236,c_1721]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1732,plain,
% 7.53/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1057]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_10461,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X1_52)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_10447,c_1711]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1117,plain,
% 7.53/1.49      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) = iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1079]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11875,plain,
% 7.53/1.49      ( v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X1_52)) = iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_10461,c_1117]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11876,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X1_52)) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X1_52) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_11875]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11889,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK1)) = iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1732,c_11876]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11911,plain,
% 7.53/1.49      ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK1)) = iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_11889,c_33,c_35,c_36,c_2365,c_2562]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11912,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(sK1)) = iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_11911]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_22,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.53/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.53/1.49      | ~ r2_hidden(X2,u1_struct_0(X0))
% 7.53/1.49      | v2_struct_0(X1)
% 7.53/1.49      | v2_struct_0(X0)
% 7.53/1.49      | ~ l1_pre_topc(X1)
% 7.53/1.49      | ~ v2_pre_topc(X1)
% 7.53/1.49      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 7.53/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1063,plain,
% 7.53/1.49      ( ~ m1_pre_topc(X0_52,X1_52)
% 7.53/1.49      | ~ m1_subset_1(X0_53,u1_struct_0(X1_52))
% 7.53/1.49      | ~ r2_hidden(X0_53,u1_struct_0(X0_52))
% 7.53/1.49      | v2_struct_0(X1_52)
% 7.53/1.49      | v2_struct_0(X0_52)
% 7.53/1.49      | ~ l1_pre_topc(X1_52)
% 7.53/1.49      | ~ v2_pre_topc(X1_52)
% 7.53/1.49      | k1_funct_1(k4_tmap_1(X1_52,X0_52),X0_53) = X0_53 ),
% 7.53/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_1726,plain,
% 7.53/1.49      ( k1_funct_1(k4_tmap_1(X0_52,X1_52),X0_53) = X0_53
% 7.53/1.49      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | r2_hidden(X0_53,u1_struct_0(X1_52)) != iProver_top
% 7.53/1.49      | v2_struct_0(X1_52) = iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | l1_pre_topc(X0_52) != iProver_top
% 7.53/1.49      | v2_pre_topc(X0_52) != iProver_top ),
% 7.53/1.49      inference(predicate_to_equality,[status(thm)],[c_1063]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_11922,plain,
% 7.53/1.49      ( k1_funct_1(k4_tmap_1(sK1,X0_52),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X0_52,sK1) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_11912,c_1726]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_12696,plain,
% 7.53/1.49      ( v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_pre_topc(X0_52,sK1) != iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | k1_funct_1(k4_tmap_1(sK1,X0_52),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_11922,c_33,c_34,c_35]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_12697,plain,
% 7.53/1.49      ( k1_funct_1(k4_tmap_1(sK1,X0_52),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(X0_52,sK1) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_53),u1_struct_0(X0_52)) != iProver_top
% 7.53/1.49      | v2_struct_0(X0_52) = iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_12696]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_13564,plain,
% 7.53/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_13555,c_12697]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_13616,plain,
% 7.53/1.49      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_13564,c_36,c_37]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_13617,plain,
% 7.53/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_53)) = sK0(sK1,sK2,sK2,sK3,X0_53)
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_53) = iProver_top
% 7.53/1.49      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.53/1.49      inference(renaming,[status(thm)],[c_13616]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_13626,plain,
% 7.53/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.53/1.49      inference(superposition,[status(thm)],[c_1717,c_13617]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_13664,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.53/1.49      | ~ m1_pre_topc(sK2,sK1)
% 7.53/1.49      | v2_struct_0(sK1)
% 7.53/1.49      | ~ l1_pre_topc(sK1)
% 7.53/1.49      | ~ v2_pre_topc(sK1)
% 7.53/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.53/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.53/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_13626]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_14888,plain,
% 7.53/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.53/1.49      inference(global_propositional_subsumption,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_13626,c_32,c_31,c_30,c_28,c_27,c_26,c_25,c_23,c_1104,
% 7.53/1.49                 c_2232,c_2571,c_6938,c_7892,c_9267,c_13664,c_14582]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_16240,plain,
% 7.53/1.49      ( sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.53/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(light_normalisation,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_16239,c_9271,c_14888]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(c_16241,plain,
% 7.53/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.53/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.53/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.53/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.53/1.49      | v2_struct_0(sK1) = iProver_top
% 7.53/1.49      | v2_struct_0(sK2) = iProver_top
% 7.53/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.53/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.53/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.53/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.53/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.53/1.49      inference(equality_resolution_simp,[status(thm)],[c_16240]) ).
% 7.53/1.49  
% 7.53/1.49  cnf(contradiction,plain,
% 7.53/1.49      ( $false ),
% 7.53/1.49      inference(minisat,
% 7.53/1.49                [status(thm)],
% 7.53/1.49                [c_16241,c_14583,c_9268,c_7895,c_6939,c_2571,c_2562,
% 7.53/1.49                 c_2541,c_2365,c_2232,c_1104,c_23,c_40,c_25,c_39,c_26,
% 7.53/1.49                 c_38,c_27,c_37,c_36,c_35,c_34,c_33]) ).
% 7.53/1.49  
% 7.53/1.49  
% 7.53/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.53/1.49  
% 7.53/1.49  ------                               Statistics
% 7.53/1.49  
% 7.53/1.49  ------ Selected
% 7.53/1.49  
% 7.53/1.49  total_time:                             0.712
% 7.53/1.49  
%------------------------------------------------------------------------------
