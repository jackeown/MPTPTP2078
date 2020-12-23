%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:46 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3675)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f8])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
            | v5_pre_topc(X2,X0,X1) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
          | v5_pre_topc(X2,X0,X1) )
        & sK4 = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                | v5_pre_topc(X2,X0,X1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
              | ~ v5_pre_topc(sK3,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
              | v5_pre_topc(sK3,X0,X1) )
            & sK3 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
                  | ~ v5_pre_topc(X2,X0,sK2) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
                  | v5_pre_topc(X2,X0,sK2) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
                    | ~ v5_pre_topc(X2,sK1,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
                    | v5_pre_topc(X2,sK1,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
      | ~ v5_pre_topc(sK3,sK1,sK2) )
    & ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
      | v5_pre_topc(sK3,sK1,sK2) )
    & sK3 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f35,f34,f33,f32])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v4_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,
    ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1181,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1890,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1181])).

cnf(c_15,negated_conjecture,
    ( sK3 = sK4 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1185,negated_conjecture,
    ( sK3 = sK4 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1916,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1890,c_1185])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1191,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v5_pre_topc(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | m1_subset_1(sK0(X0_49,X1_49,X0_48),k1_zfmisc_1(u1_struct_0(X1_49)))
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1881,plain,
    ( v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | v5_pre_topc(X0_48,X0_49,X1_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | m1_subset_1(sK0(X0_49,X1_49,X0_48),k1_zfmisc_1(u1_struct_0(X1_49))) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1191])).

cnf(c_2772,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1916,c_1881])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1180,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1891,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1180])).

cnf(c_1913,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1891,c_1185])).

cnf(c_3116,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2772,c_27,c_29,c_33,c_1913])).

cnf(c_3117,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3116])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1184,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1887,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1184])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1194,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | k8_relset_1(X0_50,X1_50,X0_48,X1_48) = k10_relat_1(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1878,plain,
    ( k8_relset_1(X0_50,X1_50,X0_48,X1_48) = k10_relat_1(X0_48,X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1194])).

cnf(c_2236,plain,
    ( k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2),sK4,X0_48) = k10_relat_1(sK4,X0_48) ),
    inference(superposition,[status(thm)],[c_1887,c_1878])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1190,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ v5_pre_topc(X0_48,X0_49,X1_49)
    | ~ v4_pre_topc(X1_48,X1_49)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_48,X1_48),X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(X1_49)))
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1882,plain,
    ( v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | v5_pre_topc(X0_48,X0_49,X1_49) != iProver_top
    | v4_pre_topc(X1_48,X1_49) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_48,X1_48),X0_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(X1_49))) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_2809,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v4_pre_topc(X0_48,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_48),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2236,c_1882])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_34,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_50,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_52,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1189,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(X0_50)))
    | l1_pre_topc(g1_pre_topc(X0_50,X0_48)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2123,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_49))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49))) ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_2124,plain,
    ( m1_subset_1(u1_pre_topc(X0_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_49)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2123])).

cnf(c_2126,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2124])).

cnf(c_3766,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v4_pre_topc(X0_48,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_48),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2809,c_27,c_29,c_33,c_34,c_35,c_52,c_2126])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2,plain,
    ( r1_tarski(k8_relset_1(X0,X1,X2,X3),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_329,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | X3 != X1
    | k8_relset_1(X3,X4,X2,X5) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_1176,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | m1_subset_1(k8_relset_1(X0_50,X1_50,X0_48,X1_48),k1_zfmisc_1(X0_50))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_330])).

cnf(c_1895,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(k8_relset_1(X0_50,X1_50,X0_48,X1_48),k1_zfmisc_1(X0_50)) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1176])).

cnf(c_3213,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_48),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2236,c_1895])).

cnf(c_3556,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_48),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3213,c_33,c_35])).

cnf(c_10,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_474,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_475,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_24])).

cnf(c_480,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(renaming,[status(thm)],[c_479])).

cnf(c_1169,plain,
    ( ~ v4_pre_topc(X0_48,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0_48,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(subtyping,[status(esa)],[c_480])).

cnf(c_1902,plain,
    ( v4_pre_topc(X0_48,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v4_pre_topc(X0_48,sK1) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1169])).

cnf(c_3564,plain,
    ( v4_pre_topc(k10_relat_1(sK4,X0_48),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_48),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3556,c_1902])).

cnf(c_3777,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v4_pre_topc(X0_48,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_48),sK1) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3766,c_3564])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_432,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_433,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_24])).

cnf(c_438,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_437])).

cnf(c_1171,plain,
    ( v4_pre_topc(X0_48,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0_48,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_438])).

cnf(c_1900,plain,
    ( v4_pre_topc(X0_48,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v4_pre_topc(X0_48,sK1) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1193,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v5_pre_topc(X0_48,X0_49,X1_49)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_48,sK0(X0_49,X1_49,X0_48)),X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1879,plain,
    ( v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | v5_pre_topc(X0_48,X0_49,X1_49) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_48,sK0(X0_49,X1_49,X0_48)),X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1193])).

cnf(c_2618,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2236,c_1879])).

cnf(c_3757,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2618,c_27,c_29,c_33,c_34,c_35,c_52,c_2126])).

cnf(c_3763,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) != iProver_top
    | m1_subset_1(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1900,c_3757])).

cnf(c_14,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1186,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1886,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1186])).

cnf(c_1931,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1886,c_1185])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1192,plain,
    ( ~ v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v5_pre_topc(X0_48,X0_49,X1_49)
    | v4_pre_topc(sK0(X0_49,X1_49,X0_48),X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ l1_pre_topc(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1880,plain,
    ( v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | v5_pre_topc(X0_48,X0_49,X1_49) = iProver_top
    | v4_pre_topc(sK0(X0_49,X1_49,X0_48),X1_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_2696,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_1880])).

cnf(c_2771,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_1881])).

cnf(c_3168,plain,
    ( m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2771,c_27,c_29,c_33,c_34,c_52,c_2126])).

cnf(c_3169,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3168])).

cnf(c_2237,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0_48) = k10_relat_1(sK4,X0_48) ),
    inference(superposition,[status(thm)],[c_1916,c_1878])).

cnf(c_2810,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | v4_pre_topc(X0_48,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_48),sK1) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_1882])).

cnf(c_3451,plain,
    ( v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | v4_pre_topc(X0_48,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_48),sK1) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2810,c_27,c_29,c_33,c_1913,c_1916])).

cnf(c_3462,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3169,c_3451])).

cnf(c_3944,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | m1_subset_1(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3763,c_27,c_29,c_33,c_34,c_35,c_52,c_1931,c_2126,c_2696,c_3462,c_3675])).

cnf(c_3214,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_48),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_1895])).

cnf(c_3487,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_48),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3214,c_33,c_1916])).

cnf(c_3950,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3944,c_3487])).

cnf(c_4712,plain,
    ( v4_pre_topc(X0_48,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_48),sK1) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3777,c_3950])).

cnf(c_4722,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_4712])).

cnf(c_2619,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_1879])).

cnf(c_3401,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2619,c_27,c_29,c_33,c_1913,c_1916])).

cnf(c_2697,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1916,c_1880])).

cnf(c_3109,plain,
    ( v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2697,c_27,c_29,c_33,c_1913])).

cnf(c_3110,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3109])).

cnf(c_13,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1187,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1885,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1187])).

cnf(c_1940,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1885,c_1185])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4722,c_3950,c_3401,c_3110,c_1940])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.32/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/1.00  
% 2.32/1.00  ------  iProver source info
% 2.32/1.00  
% 2.32/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.32/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/1.00  git: non_committed_changes: false
% 2.32/1.00  git: last_make_outside_of_git: false
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     num_symb
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       true
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  ------ Parsing...
% 2.32/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/1.00  ------ Proving...
% 2.32/1.00  ------ Problem Properties 
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  clauses                                 27
% 2.32/1.00  conjectures                             11
% 2.32/1.00  EPR                                     5
% 2.32/1.00  Horn                                    24
% 2.32/1.00  unary                                   9
% 2.32/1.00  binary                                  5
% 2.32/1.00  lits                                    76
% 2.32/1.00  lits eq                                 2
% 2.32/1.00  fd_pure                                 0
% 2.32/1.00  fd_pseudo                               0
% 2.32/1.00  fd_cond                                 0
% 2.32/1.00  fd_pseudo_cond                          0
% 2.32/1.00  AC symbols                              0
% 2.32/1.00  
% 2.32/1.00  ------ Schedule dynamic 5 is on 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  Current options:
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     none
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       false
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ Proving...
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  % SZS status Theorem for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  fof(f8,conjecture,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f9,negated_conjecture,(
% 2.32/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.32/1.00    inference(negated_conjecture,[],[f8])).
% 2.32/1.00  
% 2.32/1.00  fof(f22,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f9])).
% 2.32/1.00  
% 2.32/1.00  fof(f23,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.32/1.00    inference(flattening,[],[f22])).
% 2.32/1.00  
% 2.32/1.00  fof(f30,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.32/1.00    inference(nnf_transformation,[],[f23])).
% 2.32/1.00  
% 2.32/1.00  fof(f31,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.32/1.00    inference(flattening,[],[f30])).
% 2.32/1.00  
% 2.32/1.00  fof(f35,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => ((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & sK4 = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f34,plain,(
% 2.32/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(sK3,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(sK3,X0,X1)) & sK3 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f33,plain,(
% 2.32/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) | ~v5_pre_topc(X2,X0,sK2)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) | v5_pre_topc(X2,X0,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f32,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) | ~v5_pre_topc(X2,sK1,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) | v5_pre_topc(X2,sK1,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f36,plain,(
% 2.32/1.00    ((((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v5_pre_topc(sK3,sK1,sK2)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,sK1,sK2)) & sK3 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f35,f34,f33,f32])).
% 2.32/1.00  
% 2.32/1.00  fof(f56,plain,(
% 2.32/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f60,plain,(
% 2.32/1.00    sK3 = sK4),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f4,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f16,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f4])).
% 2.32/1.00  
% 2.32/1.00  fof(f17,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(flattening,[],[f16])).
% 2.32/1.00  
% 2.32/1.00  fof(f24,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(nnf_transformation,[],[f17])).
% 2.32/1.00  
% 2.32/1.00  fof(f25,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(rectify,[],[f24])).
% 2.32/1.00  
% 2.32/1.00  fof(f26,plain,(
% 2.32/1.00    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f27,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.32/1.00  
% 2.32/1.00  fof(f41,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f27])).
% 2.32/1.00  
% 2.32/1.00  fof(f51,plain,(
% 2.32/1.00    l1_pre_topc(sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f53,plain,(
% 2.32/1.00    l1_pre_topc(sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f57,plain,(
% 2.32/1.00    v1_funct_1(sK4)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f55,plain,(
% 2.32/1.00    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f59,plain,(
% 2.32/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f2,axiom,(
% 2.32/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f13,plain,(
% 2.32/1.00    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.00    inference(ennf_transformation,[],[f2])).
% 2.32/1.00  
% 2.32/1.00  fof(f38,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f13])).
% 2.32/1.00  
% 2.32/1.00  fof(f40,plain,(
% 2.32/1.00    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f27])).
% 2.32/1.00  
% 2.32/1.00  fof(f58,plain,(
% 2.32/1.00    v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f6,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f19,plain,(
% 2.32/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f6])).
% 2.32/1.00  
% 2.32/1.00  fof(f45,plain,(
% 2.32/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f19])).
% 2.32/1.00  
% 2.32/1.00  fof(f5,axiom,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f11,plain,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 2.32/1.00    inference(pure_predicate_removal,[],[f5])).
% 2.32/1.00  
% 2.32/1.00  fof(f18,plain,(
% 2.32/1.00    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.32/1.00    inference(ennf_transformation,[],[f11])).
% 2.32/1.00  
% 2.32/1.00  fof(f44,plain,(
% 2.32/1.00    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f18])).
% 2.32/1.00  
% 2.32/1.00  fof(f1,axiom,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f10,plain,(
% 2.32/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.32/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 2.32/1.00  
% 2.32/1.00  fof(f12,plain,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.32/1.00    inference(ennf_transformation,[],[f10])).
% 2.32/1.00  
% 2.32/1.00  fof(f37,plain,(
% 2.32/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f12])).
% 2.32/1.00  
% 2.32/1.00  fof(f3,axiom,(
% 2.32/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f14,plain,(
% 2.32/1.00    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)))),
% 2.32/1.00    inference(ennf_transformation,[],[f3])).
% 2.32/1.00  
% 2.32/1.00  fof(f15,plain,(
% 2.32/1.00    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))),
% 2.32/1.00    inference(flattening,[],[f14])).
% 2.32/1.00  
% 2.32/1.00  fof(f39,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f15])).
% 2.32/1.00  
% 2.32/1.00  fof(f7,axiom,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f20,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f7])).
% 2.32/1.00  
% 2.32/1.00  fof(f21,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/1.00    inference(flattening,[],[f20])).
% 2.32/1.00  
% 2.32/1.00  fof(f28,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/1.00    inference(nnf_transformation,[],[f21])).
% 2.32/1.00  
% 2.32/1.00  fof(f29,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/1.00    inference(flattening,[],[f28])).
% 2.32/1.00  
% 2.32/1.00  fof(f48,plain,(
% 2.32/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f29])).
% 2.32/1.00  
% 2.32/1.00  fof(f50,plain,(
% 2.32/1.00    v2_pre_topc(sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f46,plain,(
% 2.32/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f29])).
% 2.32/1.00  
% 2.32/1.00  fof(f43,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f27])).
% 2.32/1.00  
% 2.32/1.00  fof(f61,plain,(
% 2.32/1.00    v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,sK1,sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f42,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v4_pre_topc(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f27])).
% 2.32/1.00  
% 2.32/1.00  fof(f62,plain,(
% 2.32/1.00    ~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v5_pre_topc(sK3,sK1,sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  cnf(c_19,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.32/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1181,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1890,plain,
% 2.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1181]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_15,negated_conjecture,
% 2.32/1.00      ( sK3 = sK4 ),
% 2.32/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1185,negated_conjecture,
% 2.32/1.00      ( sK3 = sK4 ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1916,plain,
% 2.32/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.32/1.00      inference(light_normalisation,[status(thm)],[c_1890,c_1185]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | v5_pre_topc(X0,X1,X2)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v1_funct_1(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1191,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.32/1.00      | v5_pre_topc(X0_48,X0_49,X1_49)
% 2.32/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.32/1.00      | m1_subset_1(sK0(X0_49,X1_49,X0_48),k1_zfmisc_1(u1_struct_0(X1_49)))
% 2.32/1.00      | ~ l1_pre_topc(X0_49)
% 2.32/1.00      | ~ l1_pre_topc(X1_49)
% 2.32/1.00      | ~ v1_funct_1(X0_48) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1881,plain,
% 2.32/1.00      ( v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 2.32/1.00      | v5_pre_topc(X0_48,X0_49,X1_49) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 2.32/1.00      | m1_subset_1(sK0(X0_49,X1_49,X0_48),k1_zfmisc_1(u1_struct_0(X1_49))) = iProver_top
% 2.32/1.00      | l1_pre_topc(X1_49) != iProver_top
% 2.32/1.00      | l1_pre_topc(X0_49) != iProver_top
% 2.32/1.00      | v1_funct_1(X0_48) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1191]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2772,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.32/1.00      | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1916,c_1881]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_24,negated_conjecture,
% 2.32/1.00      ( l1_pre_topc(sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_27,plain,
% 2.32/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_22,negated_conjecture,
% 2.32/1.00      ( l1_pre_topc(sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_29,plain,
% 2.32/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_18,negated_conjecture,
% 2.32/1.00      ( v1_funct_1(sK4) ),
% 2.32/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_33,plain,
% 2.32/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_20,negated_conjecture,
% 2.32/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1180,negated_conjecture,
% 2.32/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1891,plain,
% 2.32/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1180]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1913,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(light_normalisation,[status(thm)],[c_1891,c_1185]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3116,plain,
% 2.32/1.00      ( m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_2772,c_27,c_29,c_33,c_1913]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3117,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.32/1.00      | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_3116]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_16,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
% 2.32/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1184,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1887,plain,
% 2.32/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1184]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.32/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1194,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.32/1.00      | k8_relset_1(X0_50,X1_50,X0_48,X1_48) = k10_relat_1(X0_48,X1_48) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1878,plain,
% 2.32/1.00      ( k8_relset_1(X0_50,X1_50,X0_48,X1_48) = k10_relat_1(X0_48,X1_48)
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1194]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2236,plain,
% 2.32/1.00      ( k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2),sK4,X0_48) = k10_relat_1(sK4,X0_48) ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1887,c_1878]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_6,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 2.32/1.00      | ~ v4_pre_topc(X3,X2)
% 2.32/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v1_funct_1(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1190,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.32/1.00      | ~ v5_pre_topc(X0_48,X0_49,X1_49)
% 2.32/1.00      | ~ v4_pre_topc(X1_48,X1_49)
% 2.32/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_48,X1_48),X0_49)
% 2.32/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.32/1.00      | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(X1_49)))
% 2.32/1.00      | ~ l1_pre_topc(X0_49)
% 2.32/1.00      | ~ l1_pre_topc(X1_49)
% 2.32/1.00      | ~ v1_funct_1(X0_48) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1882,plain,
% 2.32/1.00      ( v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 2.32/1.00      | v5_pre_topc(X0_48,X0_49,X1_49) != iProver_top
% 2.32/1.00      | v4_pre_topc(X1_48,X1_49) != iProver_top
% 2.32/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_48,X1_48),X0_49) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 2.32/1.00      | m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(X1_49))) != iProver_top
% 2.32/1.00      | l1_pre_topc(X1_49) != iProver_top
% 2.32/1.00      | l1_pre_topc(X0_49) != iProver_top
% 2.32/1.00      | v1_funct_1(X0_48) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1190]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2809,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(X0_48,sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,X0_48),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.32/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 2.32/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_2236,c_1882]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_17,negated_conjecture,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_34,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_35,plain,
% 2.32/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_8,plain,
% 2.32/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.32/1.00      | ~ l1_pre_topc(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_50,plain,
% 2.32/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_52,plain,
% 2.32/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_50]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_7,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.32/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1189,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(X0_50)))
% 2.32/1.00      | l1_pre_topc(g1_pre_topc(X0_50,X0_48)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2123,plain,
% 2.32/1.00      ( ~ m1_subset_1(u1_pre_topc(X0_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_49))))
% 2.32/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49))) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1189]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2124,plain,
% 2.32/1.00      ( m1_subset_1(u1_pre_topc(X0_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_49)))) != iProver_top
% 2.32/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49))) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2123]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2126,plain,
% 2.32/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 2.32/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2124]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3766,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(X0_48,sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,X0_48),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_2809,c_27,c_29,c_33,c_34,c_35,c_52,c_2126]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_0,plain,
% 2.32/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2,plain,
% 2.32/1.00      ( r1_tarski(k8_relset_1(X0,X1,X2,X3),X0)
% 2.32/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.32/1.00      | ~ v1_funct_1(X2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_329,plain,
% 2.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.32/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.32/1.00      | ~ v1_funct_1(X2)
% 2.32/1.00      | X3 != X1
% 2.32/1.00      | k8_relset_1(X3,X4,X2,X5) != X0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_2]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_330,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.00      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1))
% 2.32/1.00      | ~ v1_funct_1(X0) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_329]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1176,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.32/1.00      | m1_subset_1(k8_relset_1(X0_50,X1_50,X0_48,X1_48),k1_zfmisc_1(X0_50))
% 2.32/1.00      | ~ v1_funct_1(X0_48) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_330]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1895,plain,
% 2.32/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.32/1.00      | m1_subset_1(k8_relset_1(X0_50,X1_50,X0_48,X1_48),k1_zfmisc_1(X0_50)) = iProver_top
% 2.32/1.00      | v1_funct_1(X0_48) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1176]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3213,plain,
% 2.32/1.00      ( m1_subset_1(k10_relat_1(sK4,X0_48),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top
% 2.32/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_2236,c_1895]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3556,plain,
% 2.32/1.00      ( m1_subset_1(k10_relat_1(sK4,X0_48),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_3213,c_33,c_35]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_10,plain,
% 2.32/1.00      ( v4_pre_topc(X0,X1)
% 2.32/1.00      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.32/1.00      | ~ v2_pre_topc(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_25,negated_conjecture,
% 2.32/1.00      ( v2_pre_topc(sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_474,plain,
% 2.32/1.00      ( v4_pre_topc(X0,X1)
% 2.32/1.00      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | sK1 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_475,plain,
% 2.32/1.00      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.32/1.00      | v4_pre_topc(X0,sK1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 2.32/1.00      | ~ l1_pre_topc(sK1) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_474]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_479,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 2.32/1.00      | v4_pre_topc(X0,sK1)
% 2.32/1.00      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_475,c_24]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_480,plain,
% 2.32/1.00      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.32/1.00      | v4_pre_topc(X0,sK1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_479]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1169,plain,
% 2.32/1.00      ( ~ v4_pre_topc(X0_48,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.32/1.00      | v4_pre_topc(X0_48,sK1)
% 2.32/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_480]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1902,plain,
% 2.32/1.00      ( v4_pre_topc(X0_48,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.32/1.00      | v4_pre_topc(X0_48,sK1) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1169]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3564,plain,
% 2.32/1.00      ( v4_pre_topc(k10_relat_1(sK4,X0_48),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,X0_48),sK1) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3556,c_1902]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3777,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(X0_48,sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,X0_48),sK1) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3766,c_3564]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_12,plain,
% 2.32/1.00      ( ~ v4_pre_topc(X0,X1)
% 2.32/1.00      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | ~ v2_pre_topc(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_432,plain,
% 2.32/1.00      ( ~ v4_pre_topc(X0,X1)
% 2.32/1.00      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | sK1 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_433,plain,
% 2.32/1.00      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.32/1.00      | ~ v4_pre_topc(X0,sK1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.32/1.00      | ~ l1_pre_topc(sK1) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_432]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_437,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.32/1.00      | ~ v4_pre_topc(X0,sK1)
% 2.32/1.00      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_433,c_24]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_438,plain,
% 2.32/1.00      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.32/1.00      | ~ v4_pre_topc(X0,sK1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_437]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1171,plain,
% 2.32/1.00      ( v4_pre_topc(X0_48,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 2.32/1.00      | ~ v4_pre_topc(X0_48,sK1)
% 2.32/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_438]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1900,plain,
% 2.32/1.00      ( v4_pre_topc(X0_48,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.32/1.00      | v4_pre_topc(X0_48,sK1) != iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | v5_pre_topc(X0,X1,X2)
% 2.32/1.00      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v1_funct_1(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1193,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.32/1.00      | v5_pre_topc(X0_48,X0_49,X1_49)
% 2.32/1.00      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_48,sK0(X0_49,X1_49,X0_48)),X0_49)
% 2.32/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.32/1.00      | ~ l1_pre_topc(X0_49)
% 2.32/1.00      | ~ l1_pre_topc(X1_49)
% 2.32/1.00      | ~ v1_funct_1(X0_48) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1879,plain,
% 2.32/1.00      ( v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 2.32/1.00      | v5_pre_topc(X0_48,X0_49,X1_49) = iProver_top
% 2.32/1.00      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_48,sK0(X0_49,X1_49,X0_48)),X0_49) != iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 2.32/1.00      | l1_pre_topc(X1_49) != iProver_top
% 2.32/1.00      | l1_pre_topc(X0_49) != iProver_top
% 2.32/1.00      | v1_funct_1(X0_48) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1193]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2618,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.32/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 2.32/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_2236,c_1879]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3757,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_2618,c_27,c_29,c_33,c_34,c_35,c_52,c_2126]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3763,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) != iProver_top
% 2.32/1.00      | m1_subset_1(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1900,c_3757]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_14,negated_conjecture,
% 2.32/1.00      ( v5_pre_topc(sK3,sK1,sK2)
% 2.32/1.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1186,negated_conjecture,
% 2.32/1.00      ( v5_pre_topc(sK3,sK1,sK2)
% 2.32/1.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1886,plain,
% 2.32/1.00      ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1186]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1931,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 2.32/1.00      inference(light_normalisation,[status(thm)],[c_1886,c_1185]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | v5_pre_topc(X0,X1,X2)
% 2.32/1.00      | v4_pre_topc(sK0(X1,X2,X0),X2)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v1_funct_1(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1192,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.32/1.00      | v5_pre_topc(X0_48,X0_49,X1_49)
% 2.32/1.00      | v4_pre_topc(sK0(X0_49,X1_49,X0_48),X1_49)
% 2.32/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.32/1.00      | ~ l1_pre_topc(X0_49)
% 2.32/1.00      | ~ l1_pre_topc(X1_49)
% 2.32/1.00      | ~ v1_funct_1(X0_48) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1880,plain,
% 2.32/1.00      ( v1_funct_2(X0_48,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 2.32/1.00      | v5_pre_topc(X0_48,X0_49,X1_49) = iProver_top
% 2.32/1.00      | v4_pre_topc(sK0(X0_49,X1_49,X0_48),X1_49) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 2.32/1.00      | l1_pre_topc(X1_49) != iProver_top
% 2.32/1.00      | l1_pre_topc(X0_49) != iProver_top
% 2.32/1.00      | v1_funct_1(X0_48) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1192]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2696,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.32/1.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1887,c_1880]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2771,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.32/1.00      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.32/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1887,c_1881]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3168,plain,
% 2.32/1.00      ( m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_2771,c_27,c_29,c_33,c_34,c_52,c_2126]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3169,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.32/1.00      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_3168]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2237,plain,
% 2.32/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0_48) = k10_relat_1(sK4,X0_48) ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1916,c_1878]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2810,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,sK1,sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(X0_48,sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,X0_48),sK1) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.32/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_2237,c_1882]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3451,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,sK1,sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(X0_48,sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,X0_48),sK1) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_2810,c_27,c_29,c_33,c_1913,c_1916]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3462,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,sK1,sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4),sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),sK1) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3169,c_3451]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3944,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 2.32/1.00      | m1_subset_1(k10_relat_1(sK4,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_3763,c_27,c_29,c_33,c_34,c_35,c_52,c_1931,c_2126,
% 2.32/1.00                 c_2696,c_3462,c_3675]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3214,plain,
% 2.32/1.00      ( m1_subset_1(k10_relat_1(sK4,X0_48),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.32/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_2237,c_1895]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3487,plain,
% 2.32/1.00      ( m1_subset_1(k10_relat_1(sK4,X0_48),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_3214,c_33,c_1916]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3950,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
% 2.32/1.00      inference(forward_subsumption_resolution,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_3944,c_3487]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4712,plain,
% 2.32/1.00      ( v4_pre_topc(X0_48,sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,X0_48),sK1) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_3777,c_3950]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4722,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.32/1.00      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) != iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3117,c_4712]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2619,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top
% 2.32/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_2237,c_1879]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3401,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.32/1.00      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_2619,c_27,c_29,c_33,c_1913,c_1916]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2697,plain,
% 2.32/1.00      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.32/1.00      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.32/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1916,c_1880]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3109,plain,
% 2.32/1.00      ( v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_2697,c_27,c_29,c_33,c_1913]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3110,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.32/1.00      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_3109]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_13,negated_conjecture,
% 2.32/1.00      ( ~ v5_pre_topc(sK3,sK1,sK2)
% 2.32/1.00      | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1187,negated_conjecture,
% 2.32/1.00      ( ~ v5_pre_topc(sK3,sK1,sK2)
% 2.32/1.00      | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1885,plain,
% 2.32/1.00      ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1187]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1940,plain,
% 2.32/1.00      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 2.32/1.00      | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
% 2.32/1.00      inference(light_normalisation,[status(thm)],[c_1885,c_1185]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(contradiction,plain,
% 2.32/1.00      ( $false ),
% 2.32/1.00      inference(minisat,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_4722,c_3950,c_3401,c_3110,c_1940]) ).
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  ------                               Statistics
% 2.32/1.00  
% 2.32/1.00  ------ General
% 2.32/1.00  
% 2.32/1.00  abstr_ref_over_cycles:                  0
% 2.32/1.00  abstr_ref_under_cycles:                 0
% 2.32/1.00  gc_basic_clause_elim:                   0
% 2.32/1.00  forced_gc_time:                         0
% 2.32/1.00  parsing_time:                           0.011
% 2.32/1.00  unif_index_cands_time:                  0.
% 2.32/1.00  unif_index_add_time:                    0.
% 2.32/1.00  orderings_time:                         0.
% 2.32/1.00  out_proof_time:                         0.012
% 2.32/1.00  total_time:                             0.202
% 2.32/1.00  num_of_symbols:                         57
% 2.32/1.00  num_of_terms:                           4106
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing
% 2.32/1.00  
% 2.32/1.00  num_of_splits:                          0
% 2.32/1.00  num_of_split_atoms:                     0
% 2.32/1.00  num_of_reused_defs:                     0
% 2.32/1.00  num_eq_ax_congr_red:                    13
% 2.32/1.00  num_of_sem_filtered_clauses:            1
% 2.32/1.00  num_of_subtypes:                        3
% 2.32/1.00  monotx_restored_types:                  0
% 2.32/1.00  sat_num_of_epr_types:                   0
% 2.32/1.00  sat_num_of_non_cyclic_types:            0
% 2.32/1.00  sat_guarded_non_collapsed_types:        0
% 2.32/1.00  num_pure_diseq_elim:                    0
% 2.32/1.00  simp_replaced_by:                       0
% 2.32/1.00  res_preprocessed:                       113
% 2.32/1.00  prep_upred:                             0
% 2.32/1.00  prep_unflattend:                        28
% 2.32/1.00  smt_new_axioms:                         0
% 2.32/1.00  pred_elim_cands:                        8
% 2.32/1.00  pred_elim:                              2
% 2.32/1.00  pred_elim_cl:                           -1
% 2.32/1.00  pred_elim_cycles:                       4
% 2.32/1.00  merged_defs:                            6
% 2.32/1.00  merged_defs_ncl:                        0
% 2.32/1.00  bin_hyper_res:                          6
% 2.32/1.00  prep_cycles:                            3
% 2.32/1.00  pred_elim_time:                         0.029
% 2.32/1.00  splitting_time:                         0.
% 2.32/1.00  sem_filter_time:                        0.
% 2.32/1.00  monotx_time:                            0.
% 2.32/1.00  subtype_inf_time:                       0.
% 2.32/1.00  
% 2.32/1.00  ------ Problem properties
% 2.32/1.00  
% 2.32/1.00  clauses:                                27
% 2.32/1.00  conjectures:                            11
% 2.32/1.00  epr:                                    5
% 2.32/1.00  horn:                                   24
% 2.32/1.00  ground:                                 11
% 2.32/1.00  unary:                                  9
% 2.32/1.00  binary:                                 5
% 2.32/1.00  lits:                                   76
% 2.32/1.00  lits_eq:                                2
% 2.32/1.00  fd_pure:                                0
% 2.32/1.00  fd_pseudo:                              0
% 2.32/1.00  fd_cond:                                0
% 2.32/1.00  fd_pseudo_cond:                         0
% 2.32/1.00  ac_symbols:                             0
% 2.32/1.00  
% 2.32/1.00  ------ Propositional Solver
% 2.32/1.00  
% 2.32/1.00  prop_solver_calls:                      23
% 2.32/1.00  prop_fast_solver_calls:                 1280
% 2.32/1.00  smt_solver_calls:                       0
% 2.32/1.00  smt_fast_solver_calls:                  0
% 2.32/1.00  prop_num_of_clauses:                    1410
% 2.32/1.00  prop_preprocess_simplified:             4509
% 2.32/1.00  prop_fo_subsumed:                       74
% 2.32/1.00  prop_solver_time:                       0.
% 2.32/1.00  smt_solver_time:                        0.
% 2.32/1.00  smt_fast_solver_time:                   0.
% 2.32/1.00  prop_fast_solver_time:                  0.
% 2.32/1.00  prop_unsat_core_time:                   0.
% 2.32/1.00  
% 2.32/1.00  ------ QBF
% 2.32/1.00  
% 2.32/1.00  qbf_q_res:                              0
% 2.32/1.00  qbf_num_tautologies:                    0
% 2.32/1.00  qbf_prep_cycles:                        0
% 2.32/1.00  
% 2.32/1.00  ------ BMC1
% 2.32/1.00  
% 2.32/1.00  bmc1_current_bound:                     -1
% 2.32/1.00  bmc1_last_solved_bound:                 -1
% 2.32/1.00  bmc1_unsat_core_size:                   -1
% 2.32/1.00  bmc1_unsat_core_parents_size:           -1
% 2.32/1.00  bmc1_merge_next_fun:                    0
% 2.32/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation
% 2.32/1.00  
% 2.32/1.00  inst_num_of_clauses:                    376
% 2.32/1.00  inst_num_in_passive:                    43
% 2.32/1.00  inst_num_in_active:                     275
% 2.32/1.00  inst_num_in_unprocessed:                58
% 2.32/1.00  inst_num_of_loops:                      310
% 2.32/1.00  inst_num_of_learning_restarts:          0
% 2.32/1.00  inst_num_moves_active_passive:          31
% 2.32/1.00  inst_lit_activity:                      0
% 2.32/1.00  inst_lit_activity_moves:                0
% 2.32/1.00  inst_num_tautologies:                   0
% 2.32/1.00  inst_num_prop_implied:                  0
% 2.32/1.00  inst_num_existing_simplified:           0
% 2.32/1.00  inst_num_eq_res_simplified:             0
% 2.32/1.00  inst_num_child_elim:                    0
% 2.32/1.00  inst_num_of_dismatching_blockings:      52
% 2.32/1.00  inst_num_of_non_proper_insts:           313
% 2.32/1.00  inst_num_of_duplicates:                 0
% 2.32/1.00  inst_inst_num_from_inst_to_res:         0
% 2.32/1.00  inst_dismatching_checking_time:         0.
% 2.32/1.00  
% 2.32/1.00  ------ Resolution
% 2.32/1.00  
% 2.32/1.00  res_num_of_clauses:                     0
% 2.32/1.00  res_num_in_passive:                     0
% 2.32/1.00  res_num_in_active:                      0
% 2.32/1.00  res_num_of_loops:                       116
% 2.32/1.00  res_forward_subset_subsumed:            43
% 2.32/1.00  res_backward_subset_subsumed:           0
% 2.32/1.00  res_forward_subsumed:                   0
% 2.32/1.00  res_backward_subsumed:                  0
% 2.32/1.00  res_forward_subsumption_resolution:     0
% 2.32/1.00  res_backward_subsumption_resolution:    0
% 2.32/1.00  res_clause_to_clause_subsumption:       202
% 2.32/1.00  res_orphan_elimination:                 0
% 2.32/1.00  res_tautology_del:                      69
% 2.32/1.00  res_num_eq_res_simplified:              0
% 2.32/1.00  res_num_sel_changes:                    0
% 2.32/1.00  res_moves_from_active_to_pass:          0
% 2.32/1.00  
% 2.32/1.00  ------ Superposition
% 2.32/1.00  
% 2.32/1.00  sup_time_total:                         0.
% 2.32/1.00  sup_time_generating:                    0.
% 2.32/1.00  sup_time_sim_full:                      0.
% 2.32/1.00  sup_time_sim_immed:                     0.
% 2.32/1.00  
% 2.32/1.00  sup_num_of_clauses:                     70
% 2.32/1.00  sup_num_in_active:                      57
% 2.32/1.00  sup_num_in_passive:                     13
% 2.32/1.00  sup_num_of_loops:                       61
% 2.32/1.00  sup_fw_superposition:                   47
% 2.32/1.00  sup_bw_superposition:                   21
% 2.32/1.00  sup_immediate_simplified:               6
% 2.32/1.00  sup_given_eliminated:                   0
% 2.32/1.00  comparisons_done:                       0
% 2.32/1.00  comparisons_avoided:                    0
% 2.32/1.00  
% 2.32/1.00  ------ Simplifications
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  sim_fw_subset_subsumed:                 3
% 2.32/1.00  sim_bw_subset_subsumed:                 8
% 2.32/1.00  sim_fw_subsumed:                        2
% 2.32/1.00  sim_bw_subsumed:                        0
% 2.32/1.00  sim_fw_subsumption_res:                 1
% 2.32/1.00  sim_bw_subsumption_res:                 0
% 2.32/1.00  sim_tautology_del:                      18
% 2.32/1.00  sim_eq_tautology_del:                   0
% 2.32/1.00  sim_eq_res_simp:                        0
% 2.32/1.00  sim_fw_demodulated:                     1
% 2.32/1.00  sim_bw_demodulated:                     0
% 2.32/1.00  sim_light_normalised:                   7
% 2.32/1.00  sim_joinable_taut:                      0
% 2.32/1.00  sim_joinable_simp:                      0
% 2.32/1.00  sim_ac_normalised:                      0
% 2.32/1.00  sim_smt_subsumption:                    0
% 2.32/1.00  
%------------------------------------------------------------------------------
