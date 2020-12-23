%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:46 EST 2020

% Result     : Theorem 19.44s
% Output     : CNFRefutation 19.44s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_33593)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f44,f43,f42])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f40,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f40])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f49])).

fof(f74,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1444,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_26226,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1444])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1458,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_26212,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_1451,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
    | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X2_50))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_26219,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1451])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1447,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_26229,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1447])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1461,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | ~ l1_struct_0(X2_50)
    | ~ l1_struct_0(X1_50)
    | ~ l1_struct_0(X0_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_26209,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1461])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1468,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ m1_subset_1(X3_51,X1_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | v1_xboole_0(X1_51)
    | k3_funct_2(X1_51,X2_51,X0_51,X3_51) = k1_funct_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_26202,plain,
    ( k3_funct_2(X0_51,X1_51,X2_51,X3_51) = k1_funct_1(X2_51,X3_51)
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | m1_subset_1(X3_51,X0_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_27230,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = k1_funct_1(k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k2_tmap_1(X2_50,X1_50,X0_51,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_tmap_1(X2_50,X1_50,X0_51,X0_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26209,c_26202])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1459,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ l1_struct_0(X2_50)
    | ~ l1_struct_0(X1_50)
    | ~ l1_struct_0(X0_50)
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_26211,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1460,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ l1_struct_0(X2_50)
    | ~ l1_struct_0(X1_50)
    | ~ l1_struct_0(X0_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_26210,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_28682,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = k1_funct_1(k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27230,c_26211,c_26210])).

cnf(c_28686,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26229,c_28682])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_83,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_85,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_26620,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_50)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_26626,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26620])).

cnf(c_26619,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_50)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_26630,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26619])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1463,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_26207,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_26672,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_26226,c_26207])).

cnf(c_1079,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_1080,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1079])).

cnf(c_1081,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1080])).

cnf(c_26746,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26672,c_32,c_1081])).

cnf(c_1464,plain,
    ( l1_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_26206,plain,
    ( l1_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_26751,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_26746,c_26206])).

cnf(c_26890,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK3,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK3,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50))
    | v1_xboole_0(u1_struct_0(X0_50))
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_26891,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51)
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26890])).

cnf(c_27028,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_26229,c_26211])).

cnf(c_27072,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50)) = iProver_top
    | l1_struct_0(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27028,c_32,c_35,c_36,c_85,c_26751])).

cnf(c_27073,plain,
    ( l1_struct_0(X0_50) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_27072])).

cnf(c_28763,plain,
    ( l1_struct_0(X0_50) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51)
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28686,c_32,c_35,c_36,c_37,c_85,c_26626,c_26630,c_26751,c_26891,c_27073])).

cnf(c_28764,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51)
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_28763])).

cnf(c_28773,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26219,c_28764])).

cnf(c_1504,plain,
    ( l1_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_28820,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28773,c_1504])).

cnf(c_28821,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_28820])).

cnf(c_3,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1466,plain,
    ( ~ r2_funct_2(X0_51,X1_51,X2_51,X3_51)
    | ~ v1_funct_2(X2_51,X0_51,X1_51)
    | ~ v1_funct_2(X3_51,X0_51,X1_51)
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X3_51)
    | ~ v1_funct_1(X2_51)
    | X3_51 = X2_51 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_26204,plain,
    ( X0_51 = X1_51
    | r2_funct_2(X2_51,X3_51,X1_51,X0_51) != iProver_top
    | v1_funct_2(X1_51,X2_51,X3_51) != iProver_top
    | v1_funct_2(X0_51,X2_51,X3_51) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_27232,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26209,c_26204])).

cnf(c_1510,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_1513,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_27999,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27232,c_1510,c_1513])).

cnf(c_28000,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_27999])).

cnf(c_28843,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_28821,c_28000])).

cnf(c_28853,plain,
    ( l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
    | k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28843,c_1504])).

cnf(c_28854,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_28853])).

cnf(c_28876,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28854,c_26206])).

cnf(c_28879,plain,
    ( k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = X0_51
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51))
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_50,X0_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26212,c_28876])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1465,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50)
    | v2_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1503,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1465])).

cnf(c_1505,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1456,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50)
    | v1_funct_1(k4_tmap_1(X1_50,X0_50)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1518,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_50,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_34937,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51))
    | k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = X0_51
    | l1_pre_topc(X1_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28879,c_1503,c_1505,c_1518])).

cnf(c_34938,plain,
    ( k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = X0_51
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51))
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_34937])).

cnf(c_12,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1457,plain,
    ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50))
    | ~ m1_pre_topc(X1_50,X0_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v2_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_26213,plain,
    ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) = iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_34958,plain,
    ( k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = X0_51
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51))
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_34938,c_26213])).

cnf(c_34963,plain,
    ( k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = k4_tmap_1(X1_50,X2_50)
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),k4_tmap_1(X1_50,X2_50))) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),k4_tmap_1(X1_50,X2_50)))
    | v1_funct_2(k4_tmap_1(X1_50,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X2_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_50,X2_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26212,c_34958])).

cnf(c_26214,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_50,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_55862,plain,
    ( k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = k4_tmap_1(X1_50,X2_50)
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),k4_tmap_1(X1_50,X2_50))) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),k4_tmap_1(X1_50,X2_50)))
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_34963,c_26214,c_26213])).

cnf(c_55866,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0_50) = k4_tmap_1(sK1,X0_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50))) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2),sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50)))
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26226,c_55862])).

cnf(c_34962,plain,
    ( k2_tmap_1(X0_50,sK1,k4_tmap_1(sK1,X0_50),sK2) = sK3
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3))
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26229,c_34958])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_35274,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3))
    | k2_tmap_1(X0_50,sK1,k4_tmap_1(sK1,X0_50),sK2) = sK3
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34962,c_30,c_31,c_32,c_33,c_35,c_36,c_26751])).

cnf(c_35275,plain,
    ( k2_tmap_1(X0_50,sK1,k4_tmap_1(sK1,X0_50),sK2) = sK3
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3))
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_35274])).

cnf(c_35286,plain,
    ( k2_tmap_1(sK1,sK1,k4_tmap_1(sK1,sK1),sK2) = sK3
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3))
    | m1_pre_topc(sK1,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26226,c_35275])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_57,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_59,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_35324,plain,
    ( k2_tmap_1(sK1,sK1,k4_tmap_1(sK1,sK1),sK2) = sK3
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3))
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35286,c_30,c_32,c_59])).

cnf(c_17,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
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
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1452,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
    | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | r2_hidden(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X0_50))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_26218,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | r2_hidden(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X0_50)) = iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1452])).

cnf(c_28017,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | r2_hidden(sK0(X1_50,X0_50,X2_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_26218,c_28000])).

cnf(c_32695,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | r2_hidden(sK0(X1_50,X0_50,X2_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28017,c_1504])).

cnf(c_32696,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | r2_hidden(sK0(X1_50,X0_50,X2_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_32695])).

cnf(c_32717,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | r2_hidden(sK0(X1_50,X0_50,X2_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_32696,c_26206])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1455,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | m1_subset_1(u1_struct_0(X0_50),k1_zfmisc_1(u1_struct_0(X1_50)))
    | ~ l1_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_26215,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(u1_struct_0(X0_50),k1_zfmisc_1(u1_struct_0(X1_50))) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_0,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1469,negated_conjecture,
    ( ~ r2_hidden(X0_51,X1_51)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X2_51))
    | ~ v1_xboole_0(X2_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_26201,plain,
    ( r2_hidden(X0_51,X1_51) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_xboole_0(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1469])).

cnf(c_26765,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | r2_hidden(X0_51,u1_struct_0(X0_50)) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26215,c_26201])).

cnf(c_32720,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_struct_0(X2_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X3_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32717,c_26765])).

cnf(c_33366,plain,
    ( k2_tmap_1(sK2,sK1,sK3,X0_50) = X0_51
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26229,c_32720])).

cnf(c_1090,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_25])).

cnf(c_1091,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1090])).

cnf(c_1092,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_33506,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
    | k2_tmap_1(sK2,sK1,sK3,X0_50) = X0_51
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33366,c_30,c_31,c_32,c_33,c_35,c_36,c_1081,c_1092,c_1504,c_1505])).

cnf(c_33507,plain,
    ( k2_tmap_1(sK2,sK1,sK3,X0_50) = X0_51
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(renaming,[status(thm)],[c_33506])).

cnf(c_33521,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26229,c_33507])).

cnf(c_1454,plain,
    ( m1_pre_topc(X0_50,X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_19147,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_19148,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19147])).

cnf(c_33754,plain,
    ( l1_pre_topc(X0_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33521,c_32,c_33,c_35,c_36,c_1081,c_19148])).

cnf(c_33755,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top ),
    inference(renaming,[status(thm)],[c_33754])).

cnf(c_33764,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26226,c_33755])).

cnf(c_33829,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33764,c_32,c_33,c_34,c_35,c_36,c_1081,c_19148,c_33593])).

cnf(c_35332,plain,
    ( k2_tmap_1(sK1,sK1,k4_tmap_1(sK1,sK1),sK2) = sK3
    | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3)) ),
    inference(superposition,[status(thm)],[c_35324,c_33829])).

cnf(c_26809,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = k1_funct_1(sK3,X0_51)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26229,c_26202])).

cnf(c_27011,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = k1_funct_1(sK3,X0_51)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26809,c_35,c_36])).

cnf(c_27012,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = k1_funct_1(sK3,X0_51)
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_27011])).

cnf(c_27414,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26219,c_27012])).

cnf(c_27845,plain,
    ( v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51))
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27414,c_31,c_32,c_33,c_1081,c_1092])).

cnf(c_27846,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_27845])).

cnf(c_28019,plain,
    ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = X1_51
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51))
    | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27846,c_28000])).

cnf(c_28141,plain,
    ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = X1_51
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51))
    | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28019,c_1504,c_26751])).

cnf(c_28162,plain,
    ( k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_51,sK3))
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26229,c_28141])).

cnf(c_28272,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_51,sK3))
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28162,c_30,c_31,c_32,c_33,c_35,c_36,c_1081,c_19148,c_26751])).

cnf(c_28273,plain,
    ( k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_51,sK3))
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_28272])).

cnf(c_28284,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26229,c_28273])).

cnf(c_28344,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28284,c_35,c_36])).

cnf(c_26216,plain,
    ( m1_pre_topc(X0_50,X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1454])).

cnf(c_33765,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26216,c_33755])).

cnf(c_33862,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33765,c_32,c_1081])).

cnf(c_33880,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_28344,c_33862])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_1453,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
    | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | k3_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),X0_51,sK0(X1_50,X2_50,X0_50,X0_51,X1_51)) != k1_funct_1(X1_51,sK0(X1_50,X2_50,X0_50,X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_26217,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) != k1_funct_1(X1_51,sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1453])).

cnf(c_34126,plain,
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
    inference(superposition,[status(thm)],[c_33880,c_26217])).

cnf(c_35066,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34126,c_30,c_31,c_32,c_33,c_35,c_36,c_37,c_1081,c_1092,c_19148])).

cnf(c_35072,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_35066,c_28000])).

cnf(c_35352,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_35332,c_32,c_35,c_36,c_37,c_85,c_26751,c_35072])).

cnf(c_55897,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0_50) = k4_tmap_1(sK1,X0_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50))) = k1_funct_1(sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50)))
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_55866,c_35352])).

cnf(c_20,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1471,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1492,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_2,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1467,plain,
    ( r2_funct_2(X0_51,X1_51,X2_51,X2_51)
    | ~ v1_funct_2(X2_51,X0_51,X1_51)
    | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X2_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2075,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_4883,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_7063,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_33522,plain,
    ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
    | v1_funct_2(k4_tmap_1(sK1,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26212,c_33507])).

cnf(c_34160,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
    | k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33522,c_30,c_31,c_32])).

cnf(c_34161,plain,
    ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
    | v1_funct_2(k4_tmap_1(sK1,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(renaming,[status(thm)],[c_34160])).

cnf(c_34175,plain,
    ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26213,c_34161])).

cnf(c_34181,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34175,c_30,c_31,c_32])).

cnf(c_34182,plain,
    ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(renaming,[status(thm)],[c_34181])).

cnf(c_34195,plain,
    ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26214,c_34182])).

cnf(c_34202,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
    | l1_pre_topc(X1_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34195,c_30,c_31,c_32])).

cnf(c_34203,plain,
    ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
    inference(renaming,[status(thm)],[c_34202])).

cnf(c_34216,plain,
    ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26216,c_34203])).

cnf(c_34719,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = k4_tmap_1(sK1,sK2)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26226,c_34216])).

cnf(c_34759,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = k4_tmap_1(sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34719,c_32,c_33,c_1081,c_19148])).

cnf(c_35363,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35352,c_34759])).

cnf(c_1481,plain,
    ( ~ r2_funct_2(X0_51,X1_51,X2_51,X3_51)
    | r2_funct_2(X4_51,X5_51,X6_51,X7_51)
    | X4_51 != X0_51
    | X5_51 != X1_51
    | X6_51 != X2_51
    | X7_51 != X3_51 ),
    theory(equality)).

cnf(c_27007,plain,
    ( r2_funct_2(X0_51,X1_51,X2_51,X3_51)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | X1_51 != u1_struct_0(sK1)
    | X0_51 != u1_struct_0(sK2)
    | X3_51 != sK3
    | X2_51 != sK3 ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_29328,plain,
    ( r2_funct_2(X0_51,u1_struct_0(sK1),X1_51,X2_51)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | X0_51 != u1_struct_0(sK2)
    | X1_51 != sK3
    | X2_51 != sK3
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_27007])).

cnf(c_37160,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_51,X1_51)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | X0_51 != sK3
    | X1_51 != sK3
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_29328])).

cnf(c_56092,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | k4_tmap_1(sK1,sK2) != sK3
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_37160])).

cnf(c_56283,plain,
    ( l1_struct_0(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50))) = k1_funct_1(sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50)))
    | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0_50) = k4_tmap_1(sK1,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_55897,c_30,c_31,c_32,c_33,c_24,c_23,c_22,c_20,c_1492,c_2075,c_4883,c_7063,c_35363,c_56092])).

cnf(c_56284,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0_50) = k4_tmap_1(sK1,X0_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50))) = k1_funct_1(sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50)))
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_struct_0(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_56283])).

cnf(c_56295,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26226,c_56284])).

cnf(c_84,plain,
    ( l1_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1039,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v1_funct_1(k4_tmap_1(X0,X1))
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_1040,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_1039])).

cnf(c_1050,plain,
    ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_1051,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1050])).

cnf(c_1119,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_1120,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1119])).

cnf(c_26752,plain,
    ( l1_struct_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26751])).

cnf(c_26907,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),X0_51) = k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51)
    | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k4_tmap_1(X1_50,X0_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26212,c_26202])).

cnf(c_27934,plain,
    ( v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),X0_51) = k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51)
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26907,c_1518])).

cnf(c_27935,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),X0_51) = k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51)
    | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_27934])).

cnf(c_27948,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),X0_51) = k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27935,c_26213])).

cnf(c_27952,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k2_tmap_1(X0_50,X2_50,X0_51,X3_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26219,c_27948])).

cnf(c_30715,plain,
    ( v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k2_tmap_1(X0_50,X2_50,X0_51,X3_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27952,c_1503,c_1505])).

cnf(c_30716,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k2_tmap_1(X0_50,X2_50,X0_51,X3_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
    inference(renaming,[status(thm)],[c_30715])).

cnf(c_30738,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26226,c_30716])).

cnf(c_31170,plain,
    ( v2_pre_topc(X0_50) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30738,c_30,c_31,c_32,c_33])).

cnf(c_31171,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_31170])).

cnf(c_31190,plain,
    ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = X1_51
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51))
    | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_struct_0(X0_50) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31171,c_28000])).

cnf(c_31222,plain,
    ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = X1_51
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51))
    | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31190,c_1504,c_26751])).

cnf(c_31244,plain,
    ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = k4_tmap_1(X0_50,X1_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50)))
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26212,c_31222])).

cnf(c_1517,plain,
    ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) = iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_51270,plain,
    ( v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50)))
    | k2_tmap_1(sK2,X0_50,X0_51,X1_50) = k4_tmap_1(X0_50,X1_50)
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31244,c_1517])).

cnf(c_51271,plain,
    ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = k4_tmap_1(X0_50,X1_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50)))
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_51270])).

cnf(c_51290,plain,
    ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = k4_tmap_1(X0_50,X1_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50)))
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_51271,c_26214])).

cnf(c_51295,plain,
    ( k2_tmap_1(sK2,X0_50,k4_tmap_1(X0_50,sK2),X1_50) = k4_tmap_1(X0_50,X1_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,k4_tmap_1(X0_50,sK2),k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,k4_tmap_1(X0_50,sK2),k4_tmap_1(X0_50,X1_50)))
    | v1_funct_2(k4_tmap_1(X0_50,sK2),u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(k4_tmap_1(X0_50,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26212,c_51290])).

cnf(c_51466,plain,
    ( k2_tmap_1(sK2,X0_50,k4_tmap_1(X0_50,sK2),X1_50) = k4_tmap_1(X0_50,X1_50)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,k4_tmap_1(X0_50,sK2),k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,k4_tmap_1(X0_50,sK2),k4_tmap_1(X0_50,X1_50)))
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_struct_0(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_51295,c_26214,c_26213])).

cnf(c_51470,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26226,c_51466])).

cnf(c_34,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_51578,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
    | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51470,c_30,c_31,c_32,c_33,c_34,c_1081,c_19148,c_26751])).

cnf(c_51579,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_51578])).

cnf(c_51585,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
    | k4_tmap_1(sK1,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_51579,c_35363])).

cnf(c_51590,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_51585,c_26217])).

cnf(c_1041,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_1052,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1051])).

cnf(c_1121,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_52166,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51590,c_30,c_31,c_32,c_33,c_1041,c_1052,c_1081,c_1092,c_1121,c_19148])).

cnf(c_52173,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | k4_tmap_1(sK1,sK2) = sK3
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_52166,c_28000])).

cnf(c_52174,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | k4_tmap_1(sK1,sK2) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_52173])).

cnf(c_56362,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_56295,c_29,c_28,c_27,c_24,c_23,c_22,c_20,c_84,c_1040,c_1051,c_1120,c_1492,c_2075,c_4883,c_7063,c_26752,c_52174,c_56092])).

cnf(c_31243,plain,
    ( k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3))
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26229,c_31222])).

cnf(c_31353,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3))
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31243,c_30,c_31,c_32,c_33,c_35,c_36,c_1081,c_19148,c_26751])).

cnf(c_31354,plain,
    ( k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3))
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_31353])).

cnf(c_31366,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3))
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26212,c_31354])).

cnf(c_31434,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31366,c_30,c_31,c_32,c_34,c_1041,c_1121])).

cnf(c_56390,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3))
    | k4_tmap_1(sK1,sK2) = sK3
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_56362,c_31434])).

cnf(c_59208,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_56390,c_24,c_23,c_22,c_20,c_1492,c_2075,c_4883,c_7063,c_35363,c_56092])).

cnf(c_59211,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),sK3) = iProver_top
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
    inference(superposition,[status(thm)],[c_59208,c_26217])).

cnf(c_59212,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
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
    inference(light_normalisation,[status(thm)],[c_59211,c_56362])).

cnf(c_41,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_65870,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_59212,c_30,c_31,c_32,c_33,c_35,c_36,c_37,c_41,c_1041,c_1052,c_1081,c_1092,c_1121,c_19148])).

cnf(c_56625,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_56362,c_26218])).

cnf(c_61232,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56625,c_30,c_31,c_32,c_33,c_1041,c_1052,c_1081,c_1092,c_1121,c_19148])).

cnf(c_61233,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_61232])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1448,negated_conjecture,
    ( ~ r2_hidden(X0_51,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_26221,plain,
    ( k1_funct_1(sK3,X0_51) = X0_51
    | r2_hidden(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1448])).

cnf(c_61243,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_61233,c_26221])).

cnf(c_56624,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_56362,c_26219])).

cnf(c_58602,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56624,c_30,c_31,c_32,c_33,c_1041,c_1052,c_1081,c_1092,c_1121,c_19148])).

cnf(c_58603,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_58602])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1462,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | m1_subset_1(X0_51,u1_struct_0(X1_50))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_26208,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1462])).

cnf(c_58621,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_58603,c_26208])).

cnf(c_58867,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58621,c_33])).

cnf(c_58868,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_58867])).

cnf(c_58889,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_58868,c_26208])).

cnf(c_60013,plain,
    ( v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X1_50)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58889,c_1505])).

cnf(c_60014,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_60013])).

cnf(c_60027,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK1)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_26226,c_60014])).

cnf(c_60059,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_60027,c_30,c_32,c_33,c_1081,c_19148])).

cnf(c_60060,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_60059])).

cnf(c_61343,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_61243,c_60060])).

cnf(c_61344,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_61343])).

cnf(c_1449,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_26230,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_61354,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_61344,c_26230])).

cnf(c_27413,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X3_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_26219,c_26208])).

cnf(c_29701,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X3_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27413,c_26207])).

cnf(c_32719,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,sK2) = X1_51
    | k1_funct_1(sK3,sK0(X1_50,X0_50,sK2,X0_51,X1_51)) = sK0(X1_50,X0_50,sK2,X0_51,X1_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(sK0(X1_50,X0_50,sK2,X0_51,X1_51),u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_32717,c_26221])).

cnf(c_32931,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,sK2) = X1_51
    | k1_funct_1(sK3,sK0(X1_50,X0_50,sK2,X0_51,X1_51)) = sK0(X1_50,X0_50,sK2,X0_51,X1_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(sK0(X1_50,X0_50,sK2,X0_51,X1_51),u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32719,c_33,c_26751])).

cnf(c_32954,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,sK2) = X1_51
    | k1_funct_1(sK3,sK0(X1_50,X0_50,sK2,X0_51,X1_51)) = sK0(X1_50,X0_50,sK2,X0_51,X1_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,sK2),X1_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_29701,c_32931])).

cnf(c_36523,plain,
    ( l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,sK2),X1_51) = iProver_top
    | k1_funct_1(sK3,sK0(X1_50,X0_50,sK2,X0_51,X1_51)) = sK0(X1_50,X0_50,sK2,X0_51,X1_51)
    | k2_tmap_1(X0_50,X1_50,X0_51,sK2) = X1_51
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32954,c_30,c_32,c_33])).

cnf(c_36524,plain,
    ( k2_tmap_1(X0_50,X1_50,X0_51,sK2) = X1_51
    | k1_funct_1(sK3,sK0(X1_50,X0_50,sK2,X0_51,X1_51)) = sK0(X1_50,X0_50,sK2,X0_51,X1_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,sK2),X1_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_36523])).

cnf(c_56694,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0_51
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_56362,c_36524])).

cnf(c_56760,plain,
    ( k4_tmap_1(sK1,sK2) = X0_51
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_56694,c_56362])).

cnf(c_58152,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
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
    inference(instantiation,[status(thm)],[c_56760])).

cnf(c_61402,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_61354,c_30,c_31,c_32,c_33,c_34,c_24,c_35,c_23,c_36,c_22,c_37,c_20,c_41,c_1041,c_1052,c_1081,c_1092,c_1121,c_1492,c_2075,c_4883,c_7063,c_19148,c_56092,c_58152])).

cnf(c_65872,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) != sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3) ),
    inference(light_normalisation,[status(thm)],[c_65870,c_61402])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1450,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ r2_hidden(X0_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_51,u1_struct_0(X1_50))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50)
    | k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_26220,plain,
    ( k1_funct_1(k4_tmap_1(X0_50,X1_50),X0_51) = X0_51
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | r2_hidden(X0_51,u1_struct_0(X1_50)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1450])).

cnf(c_60077,plain,
    ( k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_60060,c_26220])).

cnf(c_60927,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_60077,c_30,c_31,c_32])).

cnf(c_60928,plain,
    ( k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_60927])).

cnf(c_60941,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0_51
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32717,c_60928])).

cnf(c_60942,plain,
    ( k4_tmap_1(sK1,sK2) = X0_51
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_60941,c_56362])).

cnf(c_60944,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60942])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65872,c_60944,c_56092,c_26751,c_19148,c_7063,c_4883,c_2075,c_1492,c_1121,c_1092,c_1081,c_1052,c_1041,c_41,c_20,c_37,c_22,c_36,c_23,c_35,c_24,c_34,c_33,c_32,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : iproveropt_run.sh %d %s
% 0.06/0.25  % Computer   : n010.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 19:40:14 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running in FOF mode
% 19.44/2.83  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.44/2.83  
% 19.44/2.83  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.44/2.83  
% 19.44/2.83  ------  iProver source info
% 19.44/2.83  
% 19.44/2.83  git: date: 2020-06-30 10:37:57 +0100
% 19.44/2.83  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.44/2.83  git: non_committed_changes: false
% 19.44/2.83  git: last_make_outside_of_git: false
% 19.44/2.83  
% 19.44/2.83  ------ 
% 19.44/2.83  ------ Parsing...
% 19.44/2.83  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  ------ Proving...
% 19.44/2.83  ------ Problem Properties 
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  clauses                                 30
% 19.44/2.83  conjectures                             11
% 19.44/2.83  EPR                                     10
% 19.44/2.83  Horn                                    21
% 19.44/2.83  unary                                   9
% 19.44/2.83  binary                                  2
% 19.44/2.83  lits                                    145
% 19.44/2.83  lits eq                                 5
% 19.44/2.83  fd_pure                                 0
% 19.44/2.83  fd_pseudo                               0
% 19.44/2.83  fd_cond                                 0
% 19.44/2.83  fd_pseudo_cond                          1
% 19.44/2.83  AC symbols                              0
% 19.44/2.83  
% 19.44/2.83  ------ Input Options Time Limit: Unbounded
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing...
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 19.44/2.83  Current options:
% 19.44/2.83  ------ 
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing...
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing...
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing...
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 12 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing...
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing...
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 12 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.44/2.83  
% 19.44/2.83  ------ Proving...
% 19.44/2.83  
% 19.44/2.83  
% 19.44/2.83  % SZS status Theorem for theBenchmark.p
% 19.44/2.83  
% 19.44/2.83  % SZS output start CNFRefutation for theBenchmark.p
% 19.44/2.83  
% 19.44/2.83  fof(f14,conjecture,(
% 19.44/2.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f15,negated_conjecture,(
% 19.44/2.83    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 19.44/2.83    inference(negated_conjecture,[],[f14])).
% 19.44/2.83  
% 19.44/2.83  fof(f37,plain,(
% 19.44/2.83    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.44/2.83    inference(ennf_transformation,[],[f15])).
% 19.44/2.83  
% 19.44/2.83  fof(f38,plain,(
% 19.44/2.83    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.44/2.83    inference(flattening,[],[f37])).
% 19.44/2.83  
% 19.44/2.83  fof(f44,plain,(
% 19.44/2.83    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 19.44/2.83    introduced(choice_axiom,[])).
% 19.44/2.83  
% 19.44/2.83  fof(f43,plain,(
% 19.44/2.83    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 19.44/2.83    introduced(choice_axiom,[])).
% 19.44/2.83  
% 19.44/2.83  fof(f42,plain,(
% 19.44/2.83    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 19.44/2.83    introduced(choice_axiom,[])).
% 19.44/2.83  
% 19.44/2.83  fof(f45,plain,(
% 19.44/2.83    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 19.44/2.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f44,f43,f42])).
% 19.44/2.83  
% 19.44/2.83  fof(f70,plain,(
% 19.44/2.83    m1_pre_topc(sK2,sK1)),
% 19.44/2.83    inference(cnf_transformation,[],[f45])).
% 19.44/2.83  
% 19.44/2.83  fof(f9,axiom,(
% 19.44/2.83    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f29,plain,(
% 19.44/2.83    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.44/2.83    inference(ennf_transformation,[],[f9])).
% 19.44/2.83  
% 19.44/2.83  fof(f30,plain,(
% 19.44/2.83    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.44/2.83    inference(flattening,[],[f29])).
% 19.44/2.83  
% 19.44/2.83  fof(f59,plain,(
% 19.44/2.83    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f30])).
% 19.44/2.83  
% 19.44/2.83  fof(f12,axiom,(
% 19.44/2.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f33,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.44/2.83    inference(ennf_transformation,[],[f12])).
% 19.44/2.83  
% 19.44/2.83  fof(f34,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.44/2.83    inference(flattening,[],[f33])).
% 19.44/2.83  
% 19.44/2.83  fof(f40,plain,(
% 19.44/2.83    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 19.44/2.83    introduced(choice_axiom,[])).
% 19.44/2.83  
% 19.44/2.83  fof(f41,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.44/2.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f40])).
% 19.44/2.83  
% 19.44/2.83  fof(f62,plain,(
% 19.44/2.83    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f41])).
% 19.44/2.83  
% 19.44/2.83  fof(f73,plain,(
% 19.44/2.83    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 19.44/2.83    inference(cnf_transformation,[],[f45])).
% 19.44/2.83  
% 19.44/2.83  fof(f8,axiom,(
% 19.44/2.83    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f27,plain,(
% 19.44/2.83    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 19.44/2.83    inference(ennf_transformation,[],[f8])).
% 19.44/2.83  
% 19.44/2.83  fof(f28,plain,(
% 19.44/2.83    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 19.44/2.83    inference(flattening,[],[f27])).
% 19.44/2.83  
% 19.44/2.83  fof(f56,plain,(
% 19.44/2.83    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f28])).
% 19.44/2.83  
% 19.44/2.83  fof(f2,axiom,(
% 19.44/2.83    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f17,plain,(
% 19.44/2.83    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 19.44/2.83    inference(ennf_transformation,[],[f2])).
% 19.44/2.83  
% 19.44/2.83  fof(f18,plain,(
% 19.44/2.83    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 19.44/2.83    inference(flattening,[],[f17])).
% 19.44/2.83  
% 19.44/2.83  fof(f47,plain,(
% 19.44/2.83    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f18])).
% 19.44/2.83  
% 19.44/2.83  fof(f54,plain,(
% 19.44/2.83    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f28])).
% 19.44/2.83  
% 19.44/2.83  fof(f55,plain,(
% 19.44/2.83    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f28])).
% 19.44/2.83  
% 19.44/2.83  fof(f68,plain,(
% 19.44/2.83    l1_pre_topc(sK1)),
% 19.44/2.83    inference(cnf_transformation,[],[f45])).
% 19.44/2.83  
% 19.44/2.83  fof(f71,plain,(
% 19.44/2.83    v1_funct_1(sK3)),
% 19.44/2.83    inference(cnf_transformation,[],[f45])).
% 19.44/2.83  
% 19.44/2.83  fof(f72,plain,(
% 19.44/2.83    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 19.44/2.83    inference(cnf_transformation,[],[f45])).
% 19.44/2.83  
% 19.44/2.83  fof(f5,axiom,(
% 19.44/2.83    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f23,plain,(
% 19.44/2.83    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 19.44/2.83    inference(ennf_transformation,[],[f5])).
% 19.44/2.83  
% 19.44/2.83  fof(f51,plain,(
% 19.44/2.83    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f23])).
% 19.44/2.83  
% 19.44/2.83  fof(f6,axiom,(
% 19.44/2.83    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f24,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.44/2.83    inference(ennf_transformation,[],[f6])).
% 19.44/2.83  
% 19.44/2.83  fof(f52,plain,(
% 19.44/2.83    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f24])).
% 19.44/2.83  
% 19.44/2.83  fof(f3,axiom,(
% 19.44/2.83    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f19,plain,(
% 19.44/2.83    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 19.44/2.83    inference(ennf_transformation,[],[f3])).
% 19.44/2.83  
% 19.44/2.83  fof(f20,plain,(
% 19.44/2.83    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 19.44/2.83    inference(flattening,[],[f19])).
% 19.44/2.83  
% 19.44/2.83  fof(f39,plain,(
% 19.44/2.83    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 19.44/2.83    inference(nnf_transformation,[],[f20])).
% 19.44/2.83  
% 19.44/2.83  fof(f48,plain,(
% 19.44/2.83    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f39])).
% 19.44/2.83  
% 19.44/2.83  fof(f4,axiom,(
% 19.44/2.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f21,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.44/2.83    inference(ennf_transformation,[],[f4])).
% 19.44/2.83  
% 19.44/2.83  fof(f22,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.44/2.83    inference(flattening,[],[f21])).
% 19.44/2.83  
% 19.44/2.83  fof(f50,plain,(
% 19.44/2.83    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f22])).
% 19.44/2.83  
% 19.44/2.83  fof(f57,plain,(
% 19.44/2.83    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f30])).
% 19.44/2.83  
% 19.44/2.83  fof(f58,plain,(
% 19.44/2.83    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f30])).
% 19.44/2.83  
% 19.44/2.83  fof(f66,plain,(
% 19.44/2.83    ~v2_struct_0(sK1)),
% 19.44/2.83    inference(cnf_transformation,[],[f45])).
% 19.44/2.83  
% 19.44/2.83  fof(f67,plain,(
% 19.44/2.83    v2_pre_topc(sK1)),
% 19.44/2.83    inference(cnf_transformation,[],[f45])).
% 19.44/2.83  
% 19.44/2.83  fof(f69,plain,(
% 19.44/2.83    ~v2_struct_0(sK2)),
% 19.44/2.83    inference(cnf_transformation,[],[f45])).
% 19.44/2.83  
% 19.44/2.83  fof(f11,axiom,(
% 19.44/2.83    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f32,plain,(
% 19.44/2.83    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 19.44/2.83    inference(ennf_transformation,[],[f11])).
% 19.44/2.83  
% 19.44/2.83  fof(f61,plain,(
% 19.44/2.83    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f32])).
% 19.44/2.83  
% 19.44/2.83  fof(f63,plain,(
% 19.44/2.83    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f41])).
% 19.44/2.83  
% 19.44/2.83  fof(f10,axiom,(
% 19.44/2.83    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f31,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.44/2.83    inference(ennf_transformation,[],[f10])).
% 19.44/2.83  
% 19.44/2.83  fof(f60,plain,(
% 19.44/2.83    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f31])).
% 19.44/2.83  
% 19.44/2.83  fof(f1,axiom,(
% 19.44/2.83    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f16,plain,(
% 19.44/2.83    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 19.44/2.83    inference(ennf_transformation,[],[f1])).
% 19.44/2.83  
% 19.44/2.83  fof(f46,plain,(
% 19.44/2.83    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f16])).
% 19.44/2.83  
% 19.44/2.83  fof(f64,plain,(
% 19.44/2.83    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f41])).
% 19.44/2.83  
% 19.44/2.83  fof(f75,plain,(
% 19.44/2.83    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 19.44/2.83    inference(cnf_transformation,[],[f45])).
% 19.44/2.83  
% 19.44/2.83  fof(f49,plain,(
% 19.44/2.83    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f39])).
% 19.44/2.83  
% 19.44/2.83  fof(f76,plain,(
% 19.44/2.83    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 19.44/2.83    inference(equality_resolution,[],[f49])).
% 19.44/2.83  
% 19.44/2.83  fof(f74,plain,(
% 19.44/2.83    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 19.44/2.83    inference(cnf_transformation,[],[f45])).
% 19.44/2.83  
% 19.44/2.83  fof(f7,axiom,(
% 19.44/2.83    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f25,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 19.44/2.83    inference(ennf_transformation,[],[f7])).
% 19.44/2.83  
% 19.44/2.83  fof(f26,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 19.44/2.83    inference(flattening,[],[f25])).
% 19.44/2.83  
% 19.44/2.83  fof(f53,plain,(
% 19.44/2.83    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f26])).
% 19.44/2.83  
% 19.44/2.83  fof(f13,axiom,(
% 19.44/2.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 19.44/2.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.44/2.83  
% 19.44/2.83  fof(f35,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.44/2.83    inference(ennf_transformation,[],[f13])).
% 19.44/2.83  
% 19.44/2.83  fof(f36,plain,(
% 19.44/2.83    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.44/2.83    inference(flattening,[],[f35])).
% 19.44/2.83  
% 19.44/2.83  fof(f65,plain,(
% 19.44/2.83    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.44/2.83    inference(cnf_transformation,[],[f36])).
% 19.44/2.83  
% 19.44/2.83  cnf(c_25,negated_conjecture,
% 19.44/2.83      ( m1_pre_topc(sK2,sK1) ),
% 19.44/2.83      inference(cnf_transformation,[],[f70]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1444,negated_conjecture,
% 19.44/2.83      ( m1_pre_topc(sK2,sK1) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_25]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26226,plain,
% 19.44/2.83      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1444]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_11,plain,
% 19.44/2.83      ( ~ m1_pre_topc(X0,X1)
% 19.44/2.83      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 19.44/2.83      | v2_struct_0(X1)
% 19.44/2.83      | ~ l1_pre_topc(X1)
% 19.44/2.83      | ~ v2_pre_topc(X1) ),
% 19.44/2.83      inference(cnf_transformation,[],[f59]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1458,plain,
% 19.44/2.83      ( ~ m1_pre_topc(X0_50,X1_50)
% 19.44/2.83      | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 19.44/2.83      | v2_struct_0(X1_50)
% 19.44/2.83      | ~ l1_pre_topc(X1_50)
% 19.44/2.83      | ~ v2_pre_topc(X1_50) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_11]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26212,plain,
% 19.44/2.83      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_18,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 19.44/2.83      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 19.44/2.83      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 19.44/2.83      | ~ m1_pre_topc(X0,X2)
% 19.44/2.83      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 19.44/2.83      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 19.44/2.83      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 19.44/2.83      | v2_struct_0(X1)
% 19.44/2.83      | v2_struct_0(X2)
% 19.44/2.83      | v2_struct_0(X0)
% 19.44/2.83      | ~ l1_pre_topc(X1)
% 19.44/2.83      | ~ l1_pre_topc(X2)
% 19.44/2.83      | ~ v2_pre_topc(X1)
% 19.44/2.83      | ~ v2_pre_topc(X2)
% 19.44/2.83      | ~ v1_funct_1(X3)
% 19.44/2.83      | ~ v1_funct_1(X4) ),
% 19.44/2.83      inference(cnf_transformation,[],[f62]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1451,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
% 19.44/2.83      | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 19.44/2.83      | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
% 19.44/2.83      | ~ m1_pre_topc(X0_50,X2_50)
% 19.44/2.83      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 19.44/2.83      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 19.44/2.83      | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X2_50))
% 19.44/2.83      | v2_struct_0(X1_50)
% 19.44/2.83      | v2_struct_0(X0_50)
% 19.44/2.83      | v2_struct_0(X2_50)
% 19.44/2.83      | ~ l1_pre_topc(X1_50)
% 19.44/2.83      | ~ l1_pre_topc(X2_50)
% 19.44/2.83      | ~ v2_pre_topc(X1_50)
% 19.44/2.83      | ~ v2_pre_topc(X2_50)
% 19.44/2.83      | ~ v1_funct_1(X0_51)
% 19.44/2.83      | ~ v1_funct_1(X1_51) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_18]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26219,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X2_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X2_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1451]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_22,negated_conjecture,
% 19.44/2.83      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 19.44/2.83      inference(cnf_transformation,[],[f73]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1447,negated_conjecture,
% 19.44/2.83      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_22]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26229,plain,
% 19.44/2.83      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1447]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_8,plain,
% 19.44/2.83      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.44/2.83      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.44/2.83      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 19.44/2.83      | ~ l1_struct_0(X3)
% 19.44/2.83      | ~ l1_struct_0(X2)
% 19.44/2.83      | ~ l1_struct_0(X1)
% 19.44/2.83      | ~ v1_funct_1(X0) ),
% 19.44/2.83      inference(cnf_transformation,[],[f56]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1461,plain,
% 19.44/2.83      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 19.44/2.83      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 19.44/2.83      | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 19.44/2.83      | ~ l1_struct_0(X2_50)
% 19.44/2.83      | ~ l1_struct_0(X1_50)
% 19.44/2.83      | ~ l1_struct_0(X0_50)
% 19.44/2.83      | ~ v1_funct_1(X0_51) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_8]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26209,plain,
% 19.44/2.83      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1461]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1,plain,
% 19.44/2.83      ( ~ v1_funct_2(X0,X1,X2)
% 19.44/2.83      | ~ m1_subset_1(X3,X1)
% 19.44/2.83      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.44/2.83      | ~ v1_funct_1(X0)
% 19.44/2.83      | v1_xboole_0(X1)
% 19.44/2.83      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 19.44/2.83      inference(cnf_transformation,[],[f47]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1468,plain,
% 19.44/2.83      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 19.44/2.83      | ~ m1_subset_1(X3_51,X1_51)
% 19.44/2.83      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 19.44/2.83      | ~ v1_funct_1(X0_51)
% 19.44/2.83      | v1_xboole_0(X1_51)
% 19.44/2.83      | k3_funct_2(X1_51,X2_51,X0_51,X3_51) = k1_funct_1(X0_51,X3_51) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_1]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26202,plain,
% 19.44/2.83      ( k3_funct_2(X0_51,X1_51,X2_51,X3_51) = k1_funct_1(X2_51,X3_51)
% 19.44/2.83      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 19.44/2.83      | m1_subset_1(X3_51,X0_51) != iProver_top
% 19.44/2.83      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 19.44/2.83      | v1_funct_1(X2_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(X0_51) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1468]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27230,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = k1_funct_1(k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(k2_tmap_1(X2_50,X1_50,X0_51,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(k2_tmap_1(X2_50,X1_50,X0_51,X0_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26209,c_26202]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_10,plain,
% 19.44/2.83      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.44/2.83      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.44/2.83      | ~ l1_struct_0(X3)
% 19.44/2.83      | ~ l1_struct_0(X2)
% 19.44/2.83      | ~ l1_struct_0(X1)
% 19.44/2.83      | ~ v1_funct_1(X0)
% 19.44/2.83      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 19.44/2.83      inference(cnf_transformation,[],[f54]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1459,plain,
% 19.44/2.83      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 19.44/2.83      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 19.44/2.83      | ~ l1_struct_0(X2_50)
% 19.44/2.83      | ~ l1_struct_0(X1_50)
% 19.44/2.83      | ~ l1_struct_0(X0_50)
% 19.44/2.83      | ~ v1_funct_1(X0_51)
% 19.44/2.83      | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_10]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26211,plain,
% 19.44/2.83      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_9,plain,
% 19.44/2.83      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.44/2.83      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 19.44/2.83      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.44/2.83      | ~ l1_struct_0(X3)
% 19.44/2.83      | ~ l1_struct_0(X2)
% 19.44/2.83      | ~ l1_struct_0(X1)
% 19.44/2.83      | ~ v1_funct_1(X0) ),
% 19.44/2.83      inference(cnf_transformation,[],[f55]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1460,plain,
% 19.44/2.83      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 19.44/2.83      | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50))
% 19.44/2.83      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 19.44/2.83      | ~ l1_struct_0(X2_50)
% 19.44/2.83      | ~ l1_struct_0(X1_50)
% 19.44/2.83      | ~ l1_struct_0(X0_50)
% 19.44/2.83      | ~ v1_funct_1(X0_51) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_9]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26210,plain,
% 19.44/2.83      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) = iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28682,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = k1_funct_1(k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(forward_subsumption_resolution,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_27230,c_26211,c_26210]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28686,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51)
% 19.44/2.83      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_struct_0(sK1) != iProver_top
% 19.44/2.83      | l1_struct_0(sK2) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26229,c_28682]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27,negated_conjecture,
% 19.44/2.83      ( l1_pre_topc(sK1) ),
% 19.44/2.83      inference(cnf_transformation,[],[f68]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_32,plain,
% 19.44/2.83      ( l1_pre_topc(sK1) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_24,negated_conjecture,
% 19.44/2.83      ( v1_funct_1(sK3) ),
% 19.44/2.83      inference(cnf_transformation,[],[f71]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_35,plain,
% 19.44/2.83      ( v1_funct_1(sK3) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_23,negated_conjecture,
% 19.44/2.83      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 19.44/2.83      inference(cnf_transformation,[],[f72]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_36,plain,
% 19.44/2.83      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_37,plain,
% 19.44/2.83      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_5,plain,
% 19.44/2.83      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 19.44/2.83      inference(cnf_transformation,[],[f51]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_83,plain,
% 19.44/2.83      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_85,plain,
% 19.44/2.83      ( l1_struct_0(sK1) = iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_83]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26620,plain,
% 19.44/2.83      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1))
% 19.44/2.83      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 19.44/2.83      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 19.44/2.83      | ~ l1_struct_0(X0_50)
% 19.44/2.83      | ~ l1_struct_0(sK1)
% 19.44/2.83      | ~ l1_struct_0(sK2)
% 19.44/2.83      | ~ v1_funct_1(sK3) ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_1460]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26626,plain,
% 19.44/2.83      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) = iProver_top
% 19.44/2.83      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_struct_0(sK1) != iProver_top
% 19.44/2.83      | l1_struct_0(sK2) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_26620]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26619,plain,
% 19.44/2.83      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 19.44/2.83      | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 19.44/2.83      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 19.44/2.83      | ~ l1_struct_0(X0_50)
% 19.44/2.83      | ~ l1_struct_0(sK1)
% 19.44/2.83      | ~ l1_struct_0(sK2)
% 19.44/2.83      | ~ v1_funct_1(sK3) ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_1461]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26630,plain,
% 19.44/2.83      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) = iProver_top
% 19.44/2.83      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_struct_0(sK1) != iProver_top
% 19.44/2.83      | l1_struct_0(sK2) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_26619]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_6,plain,
% 19.44/2.83      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 19.44/2.83      inference(cnf_transformation,[],[f52]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1463,plain,
% 19.44/2.83      ( ~ m1_pre_topc(X0_50,X1_50)
% 19.44/2.83      | ~ l1_pre_topc(X1_50)
% 19.44/2.83      | l1_pre_topc(X0_50) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_6]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26207,plain,
% 19.44/2.83      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26672,plain,
% 19.44/2.83      ( l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK2) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26226,c_26207]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1079,plain,
% 19.44/2.83      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK1 != X0 | sK2 != X1 ),
% 19.44/2.83      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1080,plain,
% 19.44/2.83      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK2) ),
% 19.44/2.83      inference(unflattening,[status(thm)],[c_1079]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1081,plain,
% 19.44/2.83      ( l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK2) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1080]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26746,plain,
% 19.44/2.83      ( l1_pre_topc(sK2) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_26672,c_32,c_1081]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1464,plain,
% 19.44/2.83      ( l1_struct_0(X0_50) | ~ l1_pre_topc(X0_50) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_5]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26206,plain,
% 19.44/2.83      ( l1_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26751,plain,
% 19.44/2.83      ( l1_struct_0(sK2) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26746,c_26206]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26890,plain,
% 19.44/2.83      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK3,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1))
% 19.44/2.83      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 19.44/2.83      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK3,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 19.44/2.83      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50))
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50))
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_1468]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26891,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51)
% 19.44/2.83      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_26890]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27028,plain,
% 19.44/2.83      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_struct_0(sK1) != iProver_top
% 19.44/2.83      | l1_struct_0(sK2) != iProver_top
% 19.44/2.83      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50)) = iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26229,c_26211]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27072,plain,
% 19.44/2.83      ( v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50)) = iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_27028,c_32,c_35,c_36,c_85,c_26751]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27073,plain,
% 19.44/2.83      ( l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_27072]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28763,plain,
% 19.44/2.83      ( l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51)
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_28686,c_32,c_35,c_36,c_37,c_85,c_26626,c_26630,
% 19.44/2.83                 c_26751,c_26891,c_27073]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28764,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),X0_51)
% 19.44/2.83      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_28763]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28773,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
% 19.44/2.83      | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26219,c_28764]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1504,plain,
% 19.44/2.83      ( l1_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28820,plain,
% 19.44/2.83      ( v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_28773,c_1504]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28821,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
% 19.44/2.83      | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_28820]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_3,plain,
% 19.44/2.83      ( ~ r2_funct_2(X0,X1,X2,X3)
% 19.44/2.83      | ~ v1_funct_2(X2,X0,X1)
% 19.44/2.83      | ~ v1_funct_2(X3,X0,X1)
% 19.44/2.83      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.44/2.83      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.44/2.83      | ~ v1_funct_1(X2)
% 19.44/2.83      | ~ v1_funct_1(X3)
% 19.44/2.83      | X3 = X2 ),
% 19.44/2.83      inference(cnf_transformation,[],[f48]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1466,plain,
% 19.44/2.83      ( ~ r2_funct_2(X0_51,X1_51,X2_51,X3_51)
% 19.44/2.83      | ~ v1_funct_2(X2_51,X0_51,X1_51)
% 19.44/2.83      | ~ v1_funct_2(X3_51,X0_51,X1_51)
% 19.44/2.83      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 19.44/2.83      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 19.44/2.83      | ~ v1_funct_1(X3_51)
% 19.44/2.83      | ~ v1_funct_1(X2_51)
% 19.44/2.83      | X3_51 = X2_51 ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_3]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26204,plain,
% 19.44/2.83      ( X0_51 = X1_51
% 19.44/2.83      | r2_funct_2(X2_51,X3_51,X1_51,X0_51) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,X2_51,X3_51) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,X2_51,X3_51) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27232,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26209,c_26204]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1510,plain,
% 19.44/2.83      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(k2_tmap_1(X0_50,X1_50,X0_51,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) = iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1513,plain,
% 19.44/2.83      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(k2_tmap_1(X0_50,X1_50,X0_51,X2_50)) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27999,plain,
% 19.44/2.83      ( v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_27232,c_1510,c_1513]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28000,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_27999]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28843,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_28821,c_28000]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28853,plain,
% 19.44/2.83      ( l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
% 19.44/2.83      | k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_28843,c_1504]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28854,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_28853]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28876,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(forward_subsumption_resolution,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_28854,c_26206]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28879,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = X0_51
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51))
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(X1_50,X0_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26212,c_28876]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_4,plain,
% 19.44/2.83      ( ~ m1_pre_topc(X0,X1)
% 19.44/2.83      | ~ l1_pre_topc(X1)
% 19.44/2.83      | ~ v2_pre_topc(X1)
% 19.44/2.83      | v2_pre_topc(X0) ),
% 19.44/2.83      inference(cnf_transformation,[],[f50]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1465,plain,
% 19.44/2.83      ( ~ m1_pre_topc(X0_50,X1_50)
% 19.44/2.83      | ~ l1_pre_topc(X1_50)
% 19.44/2.83      | ~ v2_pre_topc(X1_50)
% 19.44/2.83      | v2_pre_topc(X0_50) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_4]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1503,plain,
% 19.44/2.83      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1465]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1505,plain,
% 19.44/2.83      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_13,plain,
% 19.44/2.83      ( ~ m1_pre_topc(X0,X1)
% 19.44/2.83      | v2_struct_0(X1)
% 19.44/2.83      | ~ l1_pre_topc(X1)
% 19.44/2.83      | ~ v2_pre_topc(X1)
% 19.44/2.83      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 19.44/2.83      inference(cnf_transformation,[],[f57]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1456,plain,
% 19.44/2.83      ( ~ m1_pre_topc(X0_50,X1_50)
% 19.44/2.83      | v2_struct_0(X1_50)
% 19.44/2.83      | ~ l1_pre_topc(X1_50)
% 19.44/2.83      | ~ v2_pre_topc(X1_50)
% 19.44/2.83      | v1_funct_1(k4_tmap_1(X1_50,X0_50)) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_13]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1518,plain,
% 19.44/2.83      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(X1_50,X0_50)) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34937,plain,
% 19.44/2.83      ( v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51))
% 19.44/2.83      | k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = X0_51
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_28879,c_1503,c_1505,c_1518]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34938,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = X0_51
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51))
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_34937]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_12,plain,
% 19.44/2.83      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 19.44/2.83      | ~ m1_pre_topc(X1,X0)
% 19.44/2.83      | v2_struct_0(X0)
% 19.44/2.83      | ~ l1_pre_topc(X0)
% 19.44/2.83      | ~ v2_pre_topc(X0) ),
% 19.44/2.83      inference(cnf_transformation,[],[f58]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1457,plain,
% 19.44/2.83      ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50))
% 19.44/2.83      | ~ m1_pre_topc(X1_50,X0_50)
% 19.44/2.83      | v2_struct_0(X0_50)
% 19.44/2.83      | ~ l1_pre_topc(X0_50)
% 19.44/2.83      | ~ v2_pre_topc(X0_50) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_12]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26213,plain,
% 19.44/2.83      ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) = iProver_top
% 19.44/2.83      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34958,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = X0_51
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),X0_51))
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(forward_subsumption_resolution,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_34938,c_26213]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34963,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = k4_tmap_1(X1_50,X2_50)
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),k4_tmap_1(X1_50,X2_50))) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),k4_tmap_1(X1_50,X2_50)))
% 19.44/2.83      | v1_funct_2(k4_tmap_1(X1_50,X2_50),u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(X1_50,X2_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26212,c_34958]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26214,plain,
% 19.44/2.83      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(X1_50,X0_50)) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_55862,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,k4_tmap_1(X1_50,X0_50),X2_50) = k4_tmap_1(X1_50,X2_50)
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),k4_tmap_1(X1_50,X2_50))) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(X1_50,X0_50,X2_50,k4_tmap_1(X1_50,X0_50),k4_tmap_1(X1_50,X2_50)))
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(forward_subsumption_resolution,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_34963,c_26214,c_26213]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_55866,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50))) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2),sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50)))
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26226,c_55862]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34962,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,sK1,k4_tmap_1(sK1,X0_50),sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3))
% 19.44/2.83      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_struct_0(sK2) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26229,c_34958]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_29,negated_conjecture,
% 19.44/2.83      ( ~ v2_struct_0(sK1) ),
% 19.44/2.83      inference(cnf_transformation,[],[f66]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_30,plain,
% 19.44/2.83      ( v2_struct_0(sK1) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28,negated_conjecture,
% 19.44/2.83      ( v2_pre_topc(sK1) ),
% 19.44/2.83      inference(cnf_transformation,[],[f67]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_31,plain,
% 19.44/2.83      ( v2_pre_topc(sK1) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26,negated_conjecture,
% 19.44/2.83      ( ~ v2_struct_0(sK2) ),
% 19.44/2.83      inference(cnf_transformation,[],[f69]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33,plain,
% 19.44/2.83      ( v2_struct_0(sK2) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_35274,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3))
% 19.44/2.83      | k2_tmap_1(X0_50,sK1,k4_tmap_1(sK1,X0_50),sK2) = sK3
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_34962,c_30,c_31,c_32,c_33,c_35,c_36,c_26751]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_35275,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,sK1,k4_tmap_1(sK1,X0_50),sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_50),sK0(sK1,X0_50,sK2,k4_tmap_1(sK1,X0_50),sK3))
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_35274]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_35286,plain,
% 19.44/2.83      ( k2_tmap_1(sK1,sK1,k4_tmap_1(sK1,sK1),sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3))
% 19.44/2.83      | m1_pre_topc(sK1,sK1) != iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26226,c_35275]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_15,plain,
% 19.44/2.83      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 19.44/2.83      inference(cnf_transformation,[],[f61]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_57,plain,
% 19.44/2.83      ( m1_pre_topc(X0,X0) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_59,plain,
% 19.44/2.83      ( m1_pre_topc(sK1,sK1) = iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_57]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_35324,plain,
% 19.44/2.83      ( k2_tmap_1(sK1,sK1,k4_tmap_1(sK1,sK1),sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3))
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_35286,c_30,c_32,c_59]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_17,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 19.44/2.83      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 19.44/2.83      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 19.44/2.83      | ~ m1_pre_topc(X0,X2)
% 19.44/2.83      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 19.44/2.83      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 19.44/2.83      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 19.44/2.83      | v2_struct_0(X1)
% 19.44/2.83      | v2_struct_0(X2)
% 19.44/2.83      | v2_struct_0(X0)
% 19.44/2.83      | ~ l1_pre_topc(X1)
% 19.44/2.83      | ~ l1_pre_topc(X2)
% 19.44/2.83      | ~ v2_pre_topc(X1)
% 19.44/2.83      | ~ v2_pre_topc(X2)
% 19.44/2.83      | ~ v1_funct_1(X3)
% 19.44/2.83      | ~ v1_funct_1(X4) ),
% 19.44/2.83      inference(cnf_transformation,[],[f63]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1452,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
% 19.44/2.83      | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 19.44/2.83      | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
% 19.44/2.83      | ~ m1_pre_topc(X0_50,X2_50)
% 19.44/2.83      | r2_hidden(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X0_50))
% 19.44/2.83      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 19.44/2.83      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 19.44/2.83      | v2_struct_0(X1_50)
% 19.44/2.83      | v2_struct_0(X0_50)
% 19.44/2.83      | v2_struct_0(X2_50)
% 19.44/2.83      | ~ l1_pre_topc(X1_50)
% 19.44/2.83      | ~ l1_pre_topc(X2_50)
% 19.44/2.83      | ~ v2_pre_topc(X1_50)
% 19.44/2.83      | ~ v2_pre_topc(X2_50)
% 19.44/2.83      | ~ v1_funct_1(X0_51)
% 19.44/2.83      | ~ v1_funct_1(X1_51) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_17]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26218,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 19.44/2.83      | r2_hidden(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X0_50)) = iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X2_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X2_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1452]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28017,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | r2_hidden(sK0(X1_50,X0_50,X2_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26218,c_28000]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_32695,plain,
% 19.44/2.83      ( v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | r2_hidden(sK0(X1_50,X0_50,X2_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_28017,c_1504]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_32696,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | r2_hidden(sK0(X1_50,X0_50,X2_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_32695]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_32717,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | r2_hidden(sK0(X1_50,X0_50,X2_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.83      inference(forward_subsumption_resolution,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_32696,c_26206]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_14,plain,
% 19.44/2.83      ( ~ m1_pre_topc(X0,X1)
% 19.44/2.83      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.44/2.83      | ~ l1_pre_topc(X1) ),
% 19.44/2.83      inference(cnf_transformation,[],[f60]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1455,plain,
% 19.44/2.83      ( ~ m1_pre_topc(X0_50,X1_50)
% 19.44/2.83      | m1_subset_1(u1_struct_0(X0_50),k1_zfmisc_1(u1_struct_0(X1_50)))
% 19.44/2.83      | ~ l1_pre_topc(X1_50) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_14]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26215,plain,
% 19.44/2.83      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_subset_1(u1_struct_0(X0_50),k1_zfmisc_1(u1_struct_0(X1_50))) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_0,negated_conjecture,
% 19.44/2.83      ( ~ r2_hidden(X0,X1)
% 19.44/2.83      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 19.44/2.83      | ~ v1_xboole_0(X2) ),
% 19.44/2.83      inference(cnf_transformation,[],[f46]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1469,negated_conjecture,
% 19.44/2.83      ( ~ r2_hidden(X0_51,X1_51)
% 19.44/2.83      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X2_51))
% 19.44/2.83      | ~ v1_xboole_0(X2_51) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_0]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26201,plain,
% 19.44/2.83      ( r2_hidden(X0_51,X1_51) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(X2_51)) != iProver_top
% 19.44/2.83      | v1_xboole_0(X2_51) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1469]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26765,plain,
% 19.44/2.83      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | r2_hidden(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26215,c_26201]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_32720,plain,
% 19.44/2.83      ( k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = X1_51
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X3_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X3_50)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_32717,c_26765]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33366,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,X0_50) = X0_51
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26229,c_32720]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1090,plain,
% 19.44/2.83      ( ~ l1_pre_topc(X0)
% 19.44/2.83      | ~ v2_pre_topc(X0)
% 19.44/2.83      | v2_pre_topc(X1)
% 19.44/2.83      | sK1 != X0
% 19.44/2.83      | sK2 != X1 ),
% 19.44/2.83      inference(resolution_lifted,[status(thm)],[c_4,c_25]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1091,plain,
% 19.44/2.83      ( ~ l1_pre_topc(sK1) | ~ v2_pre_topc(sK1) | v2_pre_topc(sK2) ),
% 19.44/2.83      inference(unflattening,[status(thm)],[c_1090]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1092,plain,
% 19.44/2.83      ( l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK2) = iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1091]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33506,plain,
% 19.44/2.83      ( v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | k2_tmap_1(sK2,sK1,sK3,X0_50) = X0_51
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_33366,c_30,c_31,c_32,c_33,c_35,c_36,c_1081,c_1092,
% 19.44/2.83                 c_1504,c_1505]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33507,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,X0_50) = X0_51
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_33506]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33521,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26229,c_33507]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1454,plain,
% 19.44/2.83      ( m1_pre_topc(X0_50,X0_50) | ~ l1_pre_topc(X0_50) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_15]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_19147,plain,
% 19.44/2.83      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_1454]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_19148,plain,
% 19.44/2.83      ( m1_pre_topc(sK2,sK2) = iProver_top
% 19.44/2.83      | l1_pre_topc(sK2) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_19147]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33754,plain,
% 19.44/2.83      ( l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.83      | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_33521,c_32,c_33,c_35,c_36,c_1081,c_19148]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33755,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_33754]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33764,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26226,c_33755]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33829,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_33764,c_32,c_33,c_34,c_35,c_36,c_1081,c_19148,c_33593]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_35332,plain,
% 19.44/2.83      ( k2_tmap_1(sK1,sK1,k4_tmap_1(sK1,sK1),sK2) = sK3
% 19.44/2.83      | k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3)) = k1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK1),sK0(sK1,sK1,sK2,k4_tmap_1(sK1,sK1),sK3)) ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_35324,c_33829]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26809,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = k1_funct_1(sK3,X0_51)
% 19.44/2.83      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26229,c_26202]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27011,plain,
% 19.44/2.83      ( m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = k1_funct_1(sK3,X0_51)
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_26809,c_35,c_36]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27012,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = k1_funct_1(sK3,X0_51)
% 19.44/2.83      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_27011]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27414,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51))
% 19.44/2.83      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26219,c_27012]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27845,plain,
% 19.44/2.83      ( v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51))
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_27414,c_31,c_32,c_33,c_1081,c_1092]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27846,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51))
% 19.44/2.83      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_27845]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28019,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = X1_51
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51))
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_struct_0(sK2) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_27846,c_28000]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28141,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = X1_51
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(sK3,sK0(X0_50,sK2,X1_50,X0_51,X1_51))
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_28019,c_1504,c_26751]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28162,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_51,sK3))
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_struct_0(sK2) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26229,c_28141]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28272,plain,
% 19.44/2.83      ( v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_51,sK3))
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_28162,c_30,c_31,c_32,c_33,c_35,c_36,c_1081,c_19148,
% 19.44/2.83                 c_26751]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28273,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,X0_51,sK3))
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_28272]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28284,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
% 19.44/2.83      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26229,c_28273]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_28344,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3))
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_28284,c_35,c_36]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26216,plain,
% 19.44/2.83      ( m1_pre_topc(X0_50,X0_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1454]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33765,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26216,c_33755]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33862,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_33765,c_32,c_1081]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33880,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,sK3)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,sK3)) ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_28344,c_33862]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_16,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 19.44/2.83      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 19.44/2.83      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 19.44/2.83      | ~ m1_pre_topc(X0,X2)
% 19.44/2.83      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 19.44/2.83      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 19.44/2.83      | v2_struct_0(X1)
% 19.44/2.83      | v2_struct_0(X2)
% 19.44/2.83      | v2_struct_0(X0)
% 19.44/2.83      | ~ l1_pre_topc(X1)
% 19.44/2.83      | ~ l1_pre_topc(X2)
% 19.44/2.83      | ~ v2_pre_topc(X1)
% 19.44/2.83      | ~ v2_pre_topc(X2)
% 19.44/2.83      | ~ v1_funct_1(X3)
% 19.44/2.83      | ~ v1_funct_1(X4)
% 19.44/2.83      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
% 19.44/2.83      inference(cnf_transformation,[],[f64]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1453,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
% 19.44/2.83      | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 19.44/2.83      | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
% 19.44/2.83      | ~ m1_pre_topc(X0_50,X2_50)
% 19.44/2.83      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 19.44/2.83      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 19.44/2.83      | v2_struct_0(X1_50)
% 19.44/2.83      | v2_struct_0(X0_50)
% 19.44/2.83      | v2_struct_0(X2_50)
% 19.44/2.83      | ~ l1_pre_topc(X1_50)
% 19.44/2.83      | ~ l1_pre_topc(X2_50)
% 19.44/2.83      | ~ v2_pre_topc(X1_50)
% 19.44/2.83      | ~ v2_pre_topc(X2_50)
% 19.44/2.83      | ~ v1_funct_1(X0_51)
% 19.44/2.83      | ~ v1_funct_1(X1_51)
% 19.44/2.83      | k3_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),X0_51,sK0(X1_50,X2_50,X0_50,X0_51,X1_51)) != k1_funct_1(X1_51,sK0(X1_50,X2_50,X0_50,X0_51,X1_51)) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_16]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26217,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) != k1_funct_1(X1_51,sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
% 19.44/2.83      | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.83      inference(predicate_to_equality,[status(thm)],[c_1453]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34126,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) = iProver_top
% 19.44/2.83      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_33880,c_26217]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_35066,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_34126,c_30,c_31,c_32,c_33,c_35,c_36,c_37,c_1081,
% 19.44/2.83                 c_1092,c_19148]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_35072,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 19.44/2.83      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.83      | l1_struct_0(sK1) != iProver_top
% 19.44/2.83      | l1_struct_0(sK2) != iProver_top
% 19.44/2.83      | v1_funct_1(sK3) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_35066,c_28000]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_35352,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_35332,c_32,c_35,c_36,c_37,c_85,c_26751,c_35072]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_55897,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50))) = k1_funct_1(sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50)))
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(light_normalisation,[status(thm)],[c_55866,c_35352]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_20,negated_conjecture,
% 19.44/2.83      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 19.44/2.83      inference(cnf_transformation,[],[f75]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1471,plain,( X0_51 = X0_51 ),theory(equality) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1492,plain,
% 19.44/2.83      ( sK3 = sK3 ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_1471]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_2,plain,
% 19.44/2.83      ( r2_funct_2(X0,X1,X2,X2)
% 19.44/2.83      | ~ v1_funct_2(X2,X0,X1)
% 19.44/2.83      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.44/2.83      | ~ v1_funct_1(X2) ),
% 19.44/2.83      inference(cnf_transformation,[],[f76]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1467,plain,
% 19.44/2.83      ( r2_funct_2(X0_51,X1_51,X2_51,X2_51)
% 19.44/2.83      | ~ v1_funct_2(X2_51,X0_51,X1_51)
% 19.44/2.83      | ~ m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 19.44/2.83      | ~ v1_funct_1(X2_51) ),
% 19.44/2.83      inference(subtyping,[status(esa)],[c_2]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_2075,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 19.44/2.83      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 19.44/2.83      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 19.44/2.83      | ~ v1_funct_1(sK3) ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_1467]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_4883,plain,
% 19.44/2.83      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_1471]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_7063,plain,
% 19.44/2.83      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_1471]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_33522,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | v1_funct_2(k4_tmap_1(sK1,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26212,c_33507]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34160,plain,
% 19.44/2.83      ( v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | v1_funct_2(k4_tmap_1(sK1,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_33522,c_30,c_31,c_32]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34161,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | v1_funct_2(k4_tmap_1(sK1,X0_50),u1_struct_0(X0_50),u1_struct_0(sK1)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_34160]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34175,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26213,c_34161]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34181,plain,
% 19.44/2.83      ( v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_34175,c_30,c_31,c_32]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34182,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(sK1,X0_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_34181]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34195,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26214,c_34182]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34202,plain,
% 19.44/2.83      ( v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_34195,c_30,c_31,c_32]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34203,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X1_50)) != iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_34202]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34216,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26216,c_34203]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34719,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.83      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26226,c_34216]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_34759,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,sK3,sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_34719,c_32,c_33,c_1081,c_19148]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_35363,plain,
% 19.44/2.83      ( k4_tmap_1(sK1,sK2) = sK3
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 19.44/2.83      inference(demodulation,[status(thm)],[c_35352,c_34759]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1481,plain,
% 19.44/2.83      ( ~ r2_funct_2(X0_51,X1_51,X2_51,X3_51)
% 19.44/2.83      | r2_funct_2(X4_51,X5_51,X6_51,X7_51)
% 19.44/2.83      | X4_51 != X0_51
% 19.44/2.83      | X5_51 != X1_51
% 19.44/2.83      | X6_51 != X2_51
% 19.44/2.83      | X7_51 != X3_51 ),
% 19.44/2.83      theory(equality) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27007,plain,
% 19.44/2.83      ( r2_funct_2(X0_51,X1_51,X2_51,X3_51)
% 19.44/2.83      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 19.44/2.83      | X1_51 != u1_struct_0(sK1)
% 19.44/2.83      | X0_51 != u1_struct_0(sK2)
% 19.44/2.83      | X3_51 != sK3
% 19.44/2.83      | X2_51 != sK3 ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_1481]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_29328,plain,
% 19.44/2.83      ( r2_funct_2(X0_51,u1_struct_0(sK1),X1_51,X2_51)
% 19.44/2.83      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 19.44/2.83      | X0_51 != u1_struct_0(sK2)
% 19.44/2.83      | X1_51 != sK3
% 19.44/2.83      | X2_51 != sK3
% 19.44/2.83      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_27007]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_37160,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_51,X1_51)
% 19.44/2.83      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 19.44/2.83      | X0_51 != sK3
% 19.44/2.83      | X1_51 != sK3
% 19.44/2.83      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 19.44/2.83      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_29328]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_56092,plain,
% 19.44/2.83      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 19.44/2.83      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 19.44/2.83      | k4_tmap_1(sK1,sK2) != sK3
% 19.44/2.83      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 19.44/2.83      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 19.44/2.83      | sK3 != sK3 ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_37160]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_56283,plain,
% 19.44/2.83      ( l1_struct_0(X0_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50))) = k1_funct_1(sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50)))
% 19.44/2.83      | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0_50) = k4_tmap_1(sK1,X0_50) ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_55897,c_30,c_31,c_32,c_33,c_24,c_23,c_22,c_20,c_1492,
% 19.44/2.83                 c_2075,c_4883,c_7063,c_35363,c_56092]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_56284,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0_50) = k4_tmap_1(sK1,X0_50)
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50))) = k1_funct_1(sK3,sK0(sK1,sK2,X0_50,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,X0_50)))
% 19.44/2.83      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | l1_struct_0(X0_50) != iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_56283]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_56295,plain,
% 19.44/2.83      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
% 19.44/2.83      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_struct_0(sK2) != iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26226,c_56284]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_84,plain,
% 19.44/2.83      ( l1_struct_0(sK1) | ~ l1_pre_topc(sK1) ),
% 19.44/2.83      inference(instantiation,[status(thm)],[c_5]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1039,plain,
% 19.44/2.83      ( v2_struct_0(X0)
% 19.44/2.83      | ~ l1_pre_topc(X0)
% 19.44/2.83      | ~ v2_pre_topc(X0)
% 19.44/2.83      | v1_funct_1(k4_tmap_1(X0,X1))
% 19.44/2.83      | sK1 != X0
% 19.44/2.83      | sK2 != X1 ),
% 19.44/2.83      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1040,plain,
% 19.44/2.83      ( v2_struct_0(sK1)
% 19.44/2.83      | ~ l1_pre_topc(sK1)
% 19.44/2.83      | ~ v2_pre_topc(sK1)
% 19.44/2.83      | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 19.44/2.83      inference(unflattening,[status(thm)],[c_1039]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1050,plain,
% 19.44/2.83      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 19.44/2.83      | v2_struct_0(X0)
% 19.44/2.83      | ~ l1_pre_topc(X0)
% 19.44/2.83      | ~ v2_pre_topc(X0)
% 19.44/2.83      | sK1 != X0
% 19.44/2.83      | sK2 != X1 ),
% 19.44/2.83      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1051,plain,
% 19.44/2.83      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 19.44/2.83      | v2_struct_0(sK1)
% 19.44/2.83      | ~ l1_pre_topc(sK1)
% 19.44/2.83      | ~ v2_pre_topc(sK1) ),
% 19.44/2.83      inference(unflattening,[status(thm)],[c_1050]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1119,plain,
% 19.44/2.83      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 19.44/2.83      | v2_struct_0(X0)
% 19.44/2.83      | ~ l1_pre_topc(X0)
% 19.44/2.83      | ~ v2_pre_topc(X0)
% 19.44/2.83      | sK1 != X0
% 19.44/2.83      | sK2 != X1 ),
% 19.44/2.83      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_1120,plain,
% 19.44/2.83      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 19.44/2.83      | v2_struct_0(sK1)
% 19.44/2.83      | ~ l1_pre_topc(sK1)
% 19.44/2.83      | ~ v2_pre_topc(sK1) ),
% 19.44/2.83      inference(unflattening,[status(thm)],[c_1119]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26752,plain,
% 19.44/2.83      ( l1_struct_0(sK2) ),
% 19.44/2.83      inference(predicate_to_equality_rev,[status(thm)],[c_26751]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_26907,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),X0_51) = k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51)
% 19.44/2.83      | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(k4_tmap_1(X1_50,X0_50)) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26212,c_26202]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27934,plain,
% 19.44/2.83      ( v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),X0_51) = k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51)
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_26907,c_1518]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27935,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),X0_51) = k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51)
% 19.44/2.83      | v1_funct_2(k4_tmap_1(X1_50,X0_50),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_27934]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27948,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),X0_51) = k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51)
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(forward_subsumption_resolution,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_27935,c_26213]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_27952,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51))
% 19.44/2.83      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k2_tmap_1(X0_50,X2_50,X0_51,X3_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X3_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X2_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26219,c_27948]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_30715,plain,
% 19.44/2.83      ( v2_pre_topc(X2_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51))
% 19.44/2.83      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k2_tmap_1(X0_50,X2_50,X0_51,X3_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X3_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X2_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(global_propositional_subsumption,
% 19.44/2.83                [status(thm)],
% 19.44/2.83                [c_27952,c_1503,c_1505]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_30716,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(X1_50,X0_50),sK0(X2_50,X0_50,X3_50,X0_51,X1_51))
% 19.44/2.83      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X2_50),k2_tmap_1(X0_50,X2_50,X0_51,X3_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X3_50),u1_struct_0(X2_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X2_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 19.44/2.83      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X2_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X2_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X3_50) = iProver_top
% 19.44/2.83      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(X2_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(X2_50) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(X0_50)) = iProver_top ),
% 19.44/2.83      inference(renaming,[status(thm)],[c_30715]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_30738,plain,
% 19.44/2.83      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51))
% 19.44/2.83      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.83      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.83      | v2_struct_0(sK1) = iProver_top
% 19.44/2.83      | v2_struct_0(sK2) = iProver_top
% 19.44/2.83      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.83      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.83      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.83      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.83      inference(superposition,[status(thm)],[c_26226,c_30716]) ).
% 19.44/2.83  
% 19.44/2.83  cnf(c_31170,plain,
% 19.44/2.83      ( v2_pre_topc(X0_50) != iProver_top
% 19.44/2.83      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51))
% 19.44/2.83      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
% 19.44/2.83      | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.83      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.83      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.83      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_30738,c_30,c_31,c_32,c_33]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_31171,plain,
% 19.44/2.84      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51))
% 19.44/2.84      | r2_funct_2(u1_struct_0(X1_50),u1_struct_0(X0_50),k2_tmap_1(sK2,X0_50,X0_51,X1_50),X1_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_31170]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_31190,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = X1_51
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51))
% 19.44/2.84      | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.84      | l1_struct_0(X0_50) != iProver_top
% 19.44/2.84      | l1_struct_0(sK2) != iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_31171,c_28000]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_31222,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = X1_51
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,X1_51))
% 19.44/2.84      | v1_funct_2(X1_51,u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_31190,c_1504,c_26751]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_31244,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = k4_tmap_1(X0_50,X1_50)
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50)))
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_26212,c_31222]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_1517,plain,
% 19.44/2.84      ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50)) = iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top ),
% 19.44/2.84      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_51270,plain,
% 19.44/2.84      ( v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50)))
% 19.44/2.84      | k2_tmap_1(sK2,X0_50,X0_51,X1_50) = k4_tmap_1(X0_50,X1_50)
% 19.44/2.84      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_31244,c_1517]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_51271,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = k4_tmap_1(X0_50,X1_50)
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50)))
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(X0_50,X1_50)) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_51270]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_51290,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,X0_50,X0_51,X1_50) = k4_tmap_1(X0_50,X1_50)
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,X0_51,k4_tmap_1(X0_50,X1_50)))
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_50)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(forward_subsumption_resolution,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_51271,c_26214]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_51295,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,X0_50,k4_tmap_1(X0_50,sK2),X1_50) = k4_tmap_1(X0_50,X1_50)
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,k4_tmap_1(X0_50,sK2),k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,k4_tmap_1(X0_50,sK2),k4_tmap_1(X0_50,X1_50)))
% 19.44/2.84      | v1_funct_2(k4_tmap_1(X0_50,sK2),u1_struct_0(sK2),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(X0_50,sK2)) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_26212,c_51290]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_51466,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,X0_50,k4_tmap_1(X0_50,sK2),X1_50) = k4_tmap_1(X0_50,X1_50)
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,k4_tmap_1(X0_50,sK2),k4_tmap_1(X0_50,X1_50))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(X0_50,sK2,X1_50,k4_tmap_1(X0_50,sK2),k4_tmap_1(X0_50,X1_50)))
% 19.44/2.84      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(X1_50,sK2) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_struct_0(X1_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(forward_subsumption_resolution,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_51295,c_26214,c_26213]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_51470,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
% 19.44/2.84      | m1_pre_topc(sK2,sK1) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_struct_0(sK2) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_26226,c_51466]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_34,plain,
% 19.44/2.84      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 19.44/2.84      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_51578,plain,
% 19.44/2.84      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
% 19.44/2.84      | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_51470,c_30,c_31,c_32,c_33,c_34,c_1081,c_19148,c_26751]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_51579,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_51578]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_51585,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
% 19.44/2.84      | k4_tmap_1(sK1,sK2) = sK3 ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_51579,c_35363]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_51590,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.84      | k4_tmap_1(sK1,sK2) = sK3
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k4_tmap_1(sK1,sK2)) = iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_51585,c_26217]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_1041,plain,
% 19.44/2.84      ( v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 19.44/2.84      inference(predicate_to_equality,[status(thm)],[c_1040]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_1052,plain,
% 19.44/2.84      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top ),
% 19.44/2.84      inference(predicate_to_equality,[status(thm)],[c_1051]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_1121,plain,
% 19.44/2.84      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top ),
% 19.44/2.84      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_52166,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.84      | k4_tmap_1(sK1,sK2) = sK3
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k4_tmap_1(sK1,sK2)) = iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_51590,c_30,c_31,c_32,c_33,c_1041,c_1052,c_1081,c_1092,
% 19.44/2.84                 c_1121,c_19148]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_52173,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.84      | k4_tmap_1(sK1,sK2) = sK3
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | l1_struct_0(sK1) != iProver_top
% 19.44/2.84      | l1_struct_0(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_52166,c_28000]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_52174,plain,
% 19.44/2.84      ( ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 19.44/2.84      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 19.44/2.84      | ~ l1_struct_0(sK1)
% 19.44/2.84      | ~ l1_struct_0(sK2)
% 19.44/2.84      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 19.44/2.84      | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 19.44/2.84      | k4_tmap_1(sK1,sK2) = sK3 ),
% 19.44/2.84      inference(predicate_to_equality_rev,[status(thm)],[c_52173]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_56362,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2) ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_56295,c_29,c_28,c_27,c_24,c_23,c_22,c_20,c_84,c_1040,
% 19.44/2.84                 c_1051,c_1120,c_1492,c_2075,c_4883,c_7063,c_26752,
% 19.44/2.84                 c_52174,c_56092]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_31243,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3))
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_struct_0(sK2) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(sK3) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_26229,c_31222]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_31353,plain,
% 19.44/2.84      ( v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3))
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_31243,c_30,c_31,c_32,c_33,c_35,c_36,c_1081,c_19148,
% 19.44/2.84                 c_26751]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_31354,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,X0_51,sK2) = sK3
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,X0_51,sK3))
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_31353]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_31366,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3))
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK1) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_26212,c_31354]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_31434,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
% 19.44/2.84      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3))
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_31366,c_30,c_31,c_32,c_34,c_1041,c_1121]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_56390,plain,
% 19.44/2.84      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3))
% 19.44/2.84      | k4_tmap_1(sK1,sK2) = sK3
% 19.44/2.84      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(demodulation,[status(thm)],[c_56362,c_31434]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_59208,plain,
% 19.44/2.84      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_56390,c_24,c_23,c_22,c_20,c_1492,c_2075,c_4883,c_7063,
% 19.44/2.84                 c_35363,c_56092]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_59211,plain,
% 19.44/2.84      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3))
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),sK3) = iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 19.44/2.84      | v1_funct_1(sK3) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_59208,c_26217]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_59212,plain,
% 19.44/2.84      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3))
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 19.44/2.84      | v1_funct_1(sK3) != iProver_top ),
% 19.44/2.84      inference(light_normalisation,[status(thm)],[c_59211,c_56362]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_41,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 19.44/2.84      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_65870,plain,
% 19.44/2.84      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_59212,c_30,c_31,c_32,c_33,c_35,c_36,c_37,c_41,c_1041,
% 19.44/2.84                 c_1052,c_1081,c_1092,c_1121,c_19148]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_56625,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_56362,c_26218]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_61232,plain,
% 19.44/2.84      ( v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_56625,c_30,c_31,c_32,c_33,c_1041,c_1052,c_1081,c_1092,
% 19.44/2.84                 c_1121,c_19148]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_61233,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_61232]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_21,negated_conjecture,
% 19.44/2.84      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 19.44/2.84      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 19.44/2.84      | k1_funct_1(sK3,X0) = X0 ),
% 19.44/2.84      inference(cnf_transformation,[],[f74]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_1448,negated_conjecture,
% 19.44/2.84      ( ~ r2_hidden(X0_51,u1_struct_0(sK2))
% 19.44/2.84      | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
% 19.44/2.84      | k1_funct_1(sK3,X0_51) = X0_51 ),
% 19.44/2.84      inference(subtyping,[status(esa)],[c_21]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_26221,plain,
% 19.44/2.84      ( k1_funct_1(sK3,X0_51) = X0_51
% 19.44/2.84      | r2_hidden(X0_51,u1_struct_0(sK2)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top ),
% 19.44/2.84      inference(predicate_to_equality,[status(thm)],[c_1448]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_61243,plain,
% 19.44/2.84      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_61233,c_26221]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_56624,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_56362,c_26219]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_58602,plain,
% 19.44/2.84      ( v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_56624,c_30,c_31,c_32,c_33,c_1041,c_1052,c_1081,c_1092,
% 19.44/2.84                 c_1121,c_19148]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_58603,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK2)) = iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_58602]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_7,plain,
% 19.44/2.84      ( ~ m1_pre_topc(X0,X1)
% 19.44/2.84      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.44/2.84      | m1_subset_1(X2,u1_struct_0(X1))
% 19.44/2.84      | v2_struct_0(X1)
% 19.44/2.84      | v2_struct_0(X0)
% 19.44/2.84      | ~ l1_pre_topc(X1) ),
% 19.44/2.84      inference(cnf_transformation,[],[f53]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_1462,plain,
% 19.44/2.84      ( ~ m1_pre_topc(X0_50,X1_50)
% 19.44/2.84      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 19.44/2.84      | m1_subset_1(X0_51,u1_struct_0(X1_50))
% 19.44/2.84      | v2_struct_0(X1_50)
% 19.44/2.84      | v2_struct_0(X0_50)
% 19.44/2.84      | ~ l1_pre_topc(X1_50) ),
% 19.44/2.84      inference(subtyping,[status(esa)],[c_7]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_26208,plain,
% 19.44/2.84      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,u1_struct_0(X1_50)) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top ),
% 19.44/2.84      inference(predicate_to_equality,[status(thm)],[c_1462]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_58621,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_58603,c_26208]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_58867,plain,
% 19.44/2.84      ( v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) = iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_58621,c_33]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_58868,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_58867]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_58889,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X1_50)) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_58868,c_26208]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60013,plain,
% 19.44/2.84      ( v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X1_50)) = iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_58889,c_1505]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60014,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X1_50)) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_60013]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60027,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK1)) = iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_26226,c_60014]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60059,plain,
% 19.44/2.84      ( m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK1)) = iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_60027,c_30,c_32,c_33,c_1081,c_19148]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60060,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(sK1)) = iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_60059]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_61343,plain,
% 19.44/2.84      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_61243,c_60060]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_61344,plain,
% 19.44/2.84      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_61343]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_1449,negated_conjecture,
% 19.44/2.84      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 19.44/2.84      inference(subtyping,[status(esa)],[c_20]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_26230,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 19.44/2.84      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_61354,plain,
% 19.44/2.84      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)
% 19.44/2.84      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v1_funct_1(sK3) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_61344,c_26230]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_27413,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X3_50)) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X3_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X2_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X3_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X2_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_26219,c_26208]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_29701,plain,
% 19.44/2.84      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X3_50)) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X2_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X3_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X3_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X2_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.84      inference(forward_subsumption_resolution,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_27413,c_26207]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_32719,plain,
% 19.44/2.84      ( k2_tmap_1(X0_50,X1_50,X0_51,sK2) = X1_51
% 19.44/2.84      | k1_funct_1(sK3,sK0(X1_50,X0_50,sK2,X0_51,X1_51)) = sK0(X1_50,X0_50,sK2,X0_51,X1_51)
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(X1_51,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(X1_50,X0_50,sK2,X0_51,X1_51),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_struct_0(sK2) != iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_32717,c_26221]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_32931,plain,
% 19.44/2.84      ( k2_tmap_1(X0_50,X1_50,X0_51,sK2) = X1_51
% 19.44/2.84      | k1_funct_1(sK3,sK0(X1_50,X0_50,sK2,X0_51,X1_51)) = sK0(X1_50,X0_50,sK2,X0_51,X1_51)
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(X1_51,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK0(X1_50,X0_50,sK2,X0_51,X1_51),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_32719,c_33,c_26751]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_32954,plain,
% 19.44/2.84      ( k2_tmap_1(X0_50,X1_50,X0_51,sK2) = X1_51
% 19.44/2.84      | k1_funct_1(sK3,sK0(X1_50,X0_50,sK2,X0_51,X1_51)) = sK0(X1_50,X0_50,sK2,X0_51,X1_51)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,sK2),X1_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(X1_51,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_29701,c_32931]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_36523,plain,
% 19.44/2.84      ( l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.84      | v1_funct_2(X1_51,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,sK2),X1_51) = iProver_top
% 19.44/2.84      | k1_funct_1(sK3,sK0(X1_50,X0_50,sK2,X0_51,X1_51)) = sK0(X1_50,X0_50,sK2,X0_51,X1_51)
% 19.44/2.84      | k2_tmap_1(X0_50,X1_50,X0_51,sK2) = X1_51
% 19.44/2.84      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_32954,c_30,c_32,c_33]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_36524,plain,
% 19.44/2.84      ( k2_tmap_1(X0_50,X1_50,X0_51,sK2) = X1_51
% 19.44/2.84      | k1_funct_1(sK3,sK0(X1_50,X0_50,sK2,X0_51,X1_51)) = sK0(X1_50,X0_50,sK2,X0_51,X1_51)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,sK2),X1_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | v1_funct_2(X1_51,u1_struct_0(sK2),u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,X0_50) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1_50)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | l1_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X1_50) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(X1_51) != iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_36523]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_56694,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0_51
% 19.44/2.84      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK1) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_56362,c_36524]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_56760,plain,
% 19.44/2.84      ( k4_tmap_1(sK1,sK2) = X0_51
% 19.44/2.84      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK1) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 19.44/2.84      inference(demodulation,[status(thm)],[c_56694,c_56362]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_58152,plain,
% 19.44/2.84      ( k4_tmap_1(sK1,sK2) = sK3
% 19.44/2.84      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK1) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 19.44/2.84      | v1_funct_1(sK3) != iProver_top ),
% 19.44/2.84      inference(instantiation,[status(thm)],[c_56760]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_61402,plain,
% 19.44/2.84      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3) ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_61354,c_30,c_31,c_32,c_33,c_34,c_24,c_35,c_23,c_36,
% 19.44/2.84                 c_22,c_37,c_20,c_41,c_1041,c_1052,c_1081,c_1092,c_1121,
% 19.44/2.84                 c_1492,c_2075,c_4883,c_7063,c_19148,c_56092,c_58152]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_65872,plain,
% 19.44/2.84      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) != sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3) ),
% 19.44/2.84      inference(light_normalisation,[status(thm)],[c_65870,c_61402]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_19,plain,
% 19.44/2.84      ( ~ m1_pre_topc(X0,X1)
% 19.44/2.84      | ~ r2_hidden(X2,u1_struct_0(X0))
% 19.44/2.84      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.44/2.84      | v2_struct_0(X1)
% 19.44/2.84      | v2_struct_0(X0)
% 19.44/2.84      | ~ l1_pre_topc(X1)
% 19.44/2.84      | ~ v2_pre_topc(X1)
% 19.44/2.84      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 19.44/2.84      inference(cnf_transformation,[],[f65]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_1450,plain,
% 19.44/2.84      ( ~ m1_pre_topc(X0_50,X1_50)
% 19.44/2.84      | ~ r2_hidden(X0_51,u1_struct_0(X0_50))
% 19.44/2.84      | ~ m1_subset_1(X0_51,u1_struct_0(X1_50))
% 19.44/2.84      | v2_struct_0(X1_50)
% 19.44/2.84      | v2_struct_0(X0_50)
% 19.44/2.84      | ~ l1_pre_topc(X1_50)
% 19.44/2.84      | ~ v2_pre_topc(X1_50)
% 19.44/2.84      | k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51) = X0_51 ),
% 19.44/2.84      inference(subtyping,[status(esa)],[c_19]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_26220,plain,
% 19.44/2.84      ( k1_funct_1(k4_tmap_1(X0_50,X1_50),X0_51) = X0_51
% 19.44/2.84      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 19.44/2.84      | r2_hidden(X0_51,u1_struct_0(X1_50)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | v2_struct_0(X1_50) = iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | l1_pre_topc(X0_50) != iProver_top
% 19.44/2.84      | v2_pre_topc(X0_50) != iProver_top ),
% 19.44/2.84      inference(predicate_to_equality,[status(thm)],[c_1450]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60077,plain,
% 19.44/2.84      ( k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.84      | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_60060,c_26220]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60927,plain,
% 19.44/2.84      ( v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(global_propositional_subsumption,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_60077,c_30,c_31,c_32]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60928,plain,
% 19.44/2.84      ( k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(X0_50,sK1) != iProver_top
% 19.44/2.84      | r2_hidden(sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51),u1_struct_0(X0_50)) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(X0_50) = iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top ),
% 19.44/2.84      inference(renaming,[status(thm)],[c_60927]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60941,plain,
% 19.44/2.84      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0_51
% 19.44/2.84      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK1) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_struct_0(sK2) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 19.44/2.84      inference(superposition,[status(thm)],[c_32717,c_60928]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60942,plain,
% 19.44/2.84      ( k4_tmap_1(sK1,sK2) = X0_51
% 19.44/2.84      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0_51)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),X0_51) = iProver_top
% 19.44/2.84      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK1) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_struct_0(sK2) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(X0_51) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 19.44/2.84      inference(demodulation,[status(thm)],[c_60941,c_56362]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(c_60944,plain,
% 19.44/2.84      ( k4_tmap_1(sK1,sK2) = sK3
% 19.44/2.84      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)) = sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),sK3)
% 19.44/2.84      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 19.44/2.84      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK1) != iProver_top
% 19.44/2.84      | m1_pre_topc(sK2,sK2) != iProver_top
% 19.44/2.84      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 19.44/2.84      | v2_struct_0(sK1) = iProver_top
% 19.44/2.84      | v2_struct_0(sK2) = iProver_top
% 19.44/2.84      | l1_struct_0(sK2) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK1) != iProver_top
% 19.44/2.84      | l1_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK1) != iProver_top
% 19.44/2.84      | v2_pre_topc(sK2) != iProver_top
% 19.44/2.84      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 19.44/2.84      | v1_funct_1(sK3) != iProver_top ),
% 19.44/2.84      inference(instantiation,[status(thm)],[c_60942]) ).
% 19.44/2.84  
% 19.44/2.84  cnf(contradiction,plain,
% 19.44/2.84      ( $false ),
% 19.44/2.84      inference(minisat,
% 19.44/2.84                [status(thm)],
% 19.44/2.84                [c_65872,c_60944,c_56092,c_26751,c_19148,c_7063,c_4883,
% 19.44/2.84                 c_2075,c_1492,c_1121,c_1092,c_1081,c_1052,c_1041,c_41,
% 19.44/2.84                 c_20,c_37,c_22,c_36,c_23,c_35,c_24,c_34,c_33,c_32,c_31,
% 19.44/2.84                 c_30]) ).
% 19.44/2.84  
% 19.44/2.84  
% 19.44/2.84  % SZS output end CNFRefutation for theBenchmark.p
% 19.44/2.84  
% 19.44/2.84  ------                               Statistics
% 19.44/2.84  
% 19.44/2.84  ------ Selected
% 19.44/2.84  
% 19.44/2.84  total_time:                             2.435
% 19.44/2.84  
%------------------------------------------------------------------------------
