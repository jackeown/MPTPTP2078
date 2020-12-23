%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:53 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_9754)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f91])).

fof(f31,conjecture,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,negated_conjecture,(
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f85,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f86,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f85])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | v5_pre_topc(X2,X0,X1) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
          & v1_funct_1(X3) )
     => ( ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK7 = X2
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | v5_pre_topc(X2,X0,X1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ v5_pre_topc(sK6,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK6,X0,X1) )
            & sK6 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
                  | ~ v5_pre_topc(X2,X0,sK5) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
                  | v5_pre_topc(X2,X0,sK5) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK4,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK4,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,
    ( ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      | ~ v5_pre_topc(sK6,sK4,sK5) )
    & ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      | v5_pre_topc(sK6,sK4,sK5) )
    & sK6 = sK7
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    & v1_funct_1(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f86,f90,f89,f88,f87])).

fof(f155,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f91])).

fof(f161,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(definition_unfolding,[],[f151,f155])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f47])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f149,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f91])).

fof(f163,plain,(
    v1_funct_1(sK7) ),
    inference(definition_unfolding,[],[f149,f155])).

fof(f150,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f91])).

fof(f162,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(definition_unfolding,[],[f150,f155])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f29,axiom,(
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

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f83,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
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
    inference(cnf_transformation,[],[f83])).

fof(f170,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
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
    inference(equality_resolution,[],[f141])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f75])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f166,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f106])).

fof(f154,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(cnf_transformation,[],[f91])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f136,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f153,plain,(
    v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(cnf_transformation,[],[f91])).

fof(f30,axiom,(
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

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f84,plain,(
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
    inference(nnf_transformation,[],[f60])).

fof(f143,plain,(
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
    inference(cnf_transformation,[],[f84])).

fof(f172,plain,(
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
    inference(equality_resolution,[],[f143])).

fof(f145,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f91])).

fof(f146,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f91])).

fof(f147,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f91])).

fof(f148,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f91])).

fof(f157,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f91])).

fof(f159,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK7,sK4,sK5) ),
    inference(definition_unfolding,[],[f157,f155])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f55,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f56,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f140,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f139,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f138,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f142,plain,(
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
    inference(cnf_transformation,[],[f83])).

fof(f169,plain,(
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
    inference(equality_resolution,[],[f142])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f45])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f73])).

fof(f102,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f21,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f124,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f116,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
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
    inference(cnf_transformation,[],[f84])).

fof(f171,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
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
    inference(equality_resolution,[],[f144])).

fof(f156,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f91])).

fof(f160,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK7,sK4,sK5) ),
    inference(definition_unfolding,[],[f156,f155])).

cnf(c_57,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_3497,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_35,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_776,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_32,c_35])).

cnf(c_28,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_780,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_28,c_26])).

cnf(c_781,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_780])).

cnf(c_3488,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_6518,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK7)
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3497,c_3488])).

cnf(c_59,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f163])).

cnf(c_68,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_58,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_69,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_6979,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK7)
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6518,c_68,c_69])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3527,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6985,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | u1_struct_0(sK4) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_6979,c_3527])).

cnf(c_49,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f170])).

cnf(c_3505,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_11288,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK7)
    | v5_pre_topc(X0,X1,sK5) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK5) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_xboole_0))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6985,c_3505])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f166])).

cnf(c_11327,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK7)
    | v5_pre_topc(X0,X1,sK5) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK5) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11288,c_12])).

cnf(c_70,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_73,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_3936,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3937,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3936])).

cnf(c_27,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_22,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_27,c_22])).

cnf(c_742,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_738,c_26])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_742])).

cnf(c_3989,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | r1_tarski(k2_relat_1(sK7),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_3990,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k2_relat_1(sK7),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3989])).

cnf(c_43,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_4016,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),X0)
    | ~ r1_tarski(k2_relat_1(sK7),X0)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_4244,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(sK5))
    | ~ r1_tarski(k2_relat_1(sK7),u1_struct_0(sK5))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4016])).

cnf(c_4245,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(sK5)) = iProver_top
    | r1_tarski(k2_relat_1(sK7),u1_struct_0(sK5)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4244])).

cnf(c_3500,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_6517,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3500,c_3488])).

cnf(c_55,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_72,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_6987,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6517,c_68,c_72])).

cnf(c_6993,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_6987,c_3527])).

cnf(c_3499,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_9641,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6993,c_3499])).

cnf(c_51,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_3503,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_8882,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3500,c_3503])).

cnf(c_63,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_64,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_62,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_65,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_61,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_66,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_60,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_67,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_52,negated_conjecture,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v5_pre_topc(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_75,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v5_pre_topc(sK7,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_47,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_88,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_90,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_46,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_91,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_93,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_45,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_3958,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_3959,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3958])).

cnf(c_3961,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3959])).

cnf(c_20,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_810,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_28,c_20])).

cnf(c_814,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_810,c_26])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_814])).

cnf(c_4001,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_4002,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
    | r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4001])).

cnf(c_48,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f169])).

cnf(c_4078,plain,
    ( v5_pre_topc(sK7,X0,X1)
    | ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_4296,plain,
    ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
    | v5_pre_topc(sK7,sK4,sK5)
    | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
    | ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4078])).

cnf(c_4297,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
    | v5_pre_topc(sK7,sK4,sK5) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4296])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_4167,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK5))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ r1_tarski(k1_relat_1(sK7),X0) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_4364,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
    inference(instantiation,[status(thm)],[c_4167])).

cnf(c_4365,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4364])).

cnf(c_9360,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8882,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_72,c_73,c_75,c_90,c_93,c_3961,c_4002,c_4297,c_4365])).

cnf(c_9366,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK7)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6985,c_9360])).

cnf(c_9980,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
    | u1_struct_0(sK4) = k1_relat_1(sK7)
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9641,c_9366])).

cnf(c_3496,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_8437,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK7)
    | v1_funct_2(sK7,u1_struct_0(sK4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6985,c_3496])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3521,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6593,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3497,c_3521])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3525,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11717,plain,
    ( k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK7
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6593,c_3525])).

cnf(c_12599,plain,
    ( k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK7
    | u1_struct_0(sK4) = k1_relat_1(sK7)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK4),k1_xboole_0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6985,c_11717])).

cnf(c_12600,plain,
    ( k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK7
    | u1_struct_0(sK4) = k1_relat_1(sK7)
    | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12599,c_12])).

cnf(c_31,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_3516,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5104,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_3516])).

cnf(c_3487,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_5373,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_3487])).

cnf(c_8044,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(k1_xboole_0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5104,c_5373])).

cnf(c_24,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_8052,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8044,c_24])).

cnf(c_13327,plain,
    ( k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK7
    | u1_struct_0(sK4) = k1_relat_1(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12600,c_8052])).

cnf(c_13328,plain,
    ( k2_zfmisc_1(u1_struct_0(sK4),k1_xboole_0) = sK7
    | u1_struct_0(sK4) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_6985,c_13327])).

cnf(c_13393,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK7)
    | sK7 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13328,c_12])).

cnf(c_3506,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_12695,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3500,c_3506])).

cnf(c_4004,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | r1_tarski(k1_relat_1(sK7),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_4005,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k1_relat_1(sK7),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4004])).

cnf(c_4334,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_4335,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4334])).

cnf(c_4162,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ r1_tarski(k1_relat_1(sK7),X0) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_4349,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ r1_tarski(k1_relat_1(sK7),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4162])).

cnf(c_4350,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top
    | r1_tarski(k1_relat_1(sK7),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4349])).

cnf(c_5312,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_3958])).

cnf(c_5313,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5312])).

cnf(c_7885,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_7886,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7885])).

cnf(c_11282,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3500,c_3505])).

cnf(c_50,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f171])).

cnf(c_4096,plain,
    ( v5_pre_topc(sK7,X0,X1)
    | ~ v5_pre_topc(sK7,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_4373,plain,
    ( ~ v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK7,sK4,sK5)
    | ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    | ~ v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4096])).

cnf(c_4374,plain,
    ( v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v5_pre_topc(sK7,sK4,sK5) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4373])).

cnf(c_12107,plain,
    ( v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11282,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_72,c_73,c_75,c_4005,c_4335,c_4350,c_4374,c_5313,c_7886])).

cnf(c_14486,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12695,c_64,c_65,c_66,c_67,c_68,c_70,c_72,c_73,c_4005,c_4335,c_4350,c_5313,c_7886,c_12107])).

cnf(c_14493,plain,
    ( sK7 = k1_xboole_0
    | v5_pre_topc(sK7,g1_pre_topc(k1_relat_1(sK7),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13393,c_14486])).

cnf(c_53,negated_conjecture,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | v5_pre_topc(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_3501,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v5_pre_topc(sK7,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_14492,plain,
    ( v5_pre_topc(sK7,sK4,sK5) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3501,c_14486])).

cnf(c_3517,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_15324,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top
    | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3500,c_3517])).

cnf(c_16031,plain,
    ( v5_pre_topc(sK7,X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v5_pre_topc(sK7,X0,sK5) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k1_relat_1(sK7),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_15324,c_3503])).

cnf(c_16150,plain,
    ( v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v5_pre_topc(sK7,sK4,sK5) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k1_relat_1(sK7),u1_struct_0(sK4)) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16031])).

cnf(c_19355,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14493,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_4005,c_12107,c_14492,c_16150])).

cnf(c_19361,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
    | v1_funct_2(sK7,u1_struct_0(sK4),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6993,c_19355])).

cnf(c_21533,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK7)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9980,c_9754,c_19129])).

cnf(c_21534,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
    | u1_struct_0(sK4) = k1_relat_1(sK7) ),
    inference(renaming,[status(thm)],[c_21533])).

cnf(c_3504,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_9998,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3500,c_3504])).

cnf(c_10826,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9998,c_64,c_65,c_66,c_67,c_68,c_70,c_72,c_73,c_90,c_93,c_3961,c_4002,c_4365,c_9360])).

cnf(c_13434,plain,
    ( sK7 = k1_xboole_0
    | v5_pre_topc(sK7,g1_pre_topc(k1_relat_1(sK7),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13393,c_10826])).

cnf(c_10832,plain,
    ( v5_pre_topc(sK7,sK4,sK5) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3501,c_10826])).

cnf(c_15325,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK5)))) = iProver_top
    | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3497,c_3517])).

cnf(c_15737,plain,
    ( v5_pre_topc(sK7,X0,sK5) != iProver_top
    | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK5) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(sK5)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_15325,c_3505])).

cnf(c_15816,plain,
    ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
    | v5_pre_topc(sK7,sK4,sK5) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15737])).

cnf(c_19113,plain,
    ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13434,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_73,c_4002,c_9360,c_10832,c_15816])).

cnf(c_21568,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK7)
    | v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21534,c_19113])).

cnf(c_22217,plain,
    ( u1_struct_0(sK4) = k1_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11327,c_68,c_70,c_73,c_3937,c_3990,c_4245,c_21568])).

cnf(c_22223,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22217,c_19355])).

cnf(c_4241,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ r1_tarski(k2_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4016])).

cnf(c_4242,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | r1_tarski(k2_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4241])).

cnf(c_3986,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | r1_tarski(k2_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_3987,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
    | r1_tarski(k2_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3986])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22223,c_4242,c_3987,c_3937,c_73,c_68])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.34/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.34/1.49  
% 7.34/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.34/1.49  
% 7.34/1.49  ------  iProver source info
% 7.34/1.49  
% 7.34/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.34/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.34/1.49  git: non_committed_changes: false
% 7.34/1.49  git: last_make_outside_of_git: false
% 7.34/1.49  
% 7.34/1.49  ------ 
% 7.34/1.49  
% 7.34/1.49  ------ Input Options
% 7.34/1.49  
% 7.34/1.49  --out_options                           all
% 7.34/1.49  --tptp_safe_out                         true
% 7.34/1.49  --problem_path                          ""
% 7.34/1.49  --include_path                          ""
% 7.34/1.49  --clausifier                            res/vclausify_rel
% 7.34/1.49  --clausifier_options                    --mode clausify
% 7.34/1.49  --stdin                                 false
% 7.34/1.49  --stats_out                             all
% 7.34/1.49  
% 7.34/1.49  ------ General Options
% 7.34/1.49  
% 7.34/1.49  --fof                                   false
% 7.34/1.49  --time_out_real                         305.
% 7.34/1.49  --time_out_virtual                      -1.
% 7.34/1.49  --symbol_type_check                     false
% 7.34/1.49  --clausify_out                          false
% 7.34/1.49  --sig_cnt_out                           false
% 7.34/1.49  --trig_cnt_out                          false
% 7.34/1.49  --trig_cnt_out_tolerance                1.
% 7.34/1.49  --trig_cnt_out_sk_spl                   false
% 7.34/1.49  --abstr_cl_out                          false
% 7.34/1.49  
% 7.34/1.49  ------ Global Options
% 7.34/1.49  
% 7.34/1.49  --schedule                              default
% 7.34/1.49  --add_important_lit                     false
% 7.34/1.49  --prop_solver_per_cl                    1000
% 7.34/1.49  --min_unsat_core                        false
% 7.34/1.49  --soft_assumptions                      false
% 7.34/1.49  --soft_lemma_size                       3
% 7.34/1.49  --prop_impl_unit_size                   0
% 7.34/1.49  --prop_impl_unit                        []
% 7.34/1.49  --share_sel_clauses                     true
% 7.34/1.49  --reset_solvers                         false
% 7.34/1.49  --bc_imp_inh                            [conj_cone]
% 7.34/1.49  --conj_cone_tolerance                   3.
% 7.34/1.49  --extra_neg_conj                        none
% 7.34/1.49  --large_theory_mode                     true
% 7.34/1.49  --prolific_symb_bound                   200
% 7.34/1.49  --lt_threshold                          2000
% 7.34/1.49  --clause_weak_htbl                      true
% 7.34/1.49  --gc_record_bc_elim                     false
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing Options
% 7.34/1.49  
% 7.34/1.49  --preprocessing_flag                    true
% 7.34/1.49  --time_out_prep_mult                    0.1
% 7.34/1.49  --splitting_mode                        input
% 7.34/1.49  --splitting_grd                         true
% 7.34/1.49  --splitting_cvd                         false
% 7.34/1.49  --splitting_cvd_svl                     false
% 7.34/1.49  --splitting_nvd                         32
% 7.34/1.49  --sub_typing                            true
% 7.34/1.49  --prep_gs_sim                           true
% 7.34/1.49  --prep_unflatten                        true
% 7.34/1.49  --prep_res_sim                          true
% 7.34/1.49  --prep_upred                            true
% 7.34/1.49  --prep_sem_filter                       exhaustive
% 7.34/1.49  --prep_sem_filter_out                   false
% 7.34/1.49  --pred_elim                             true
% 7.34/1.49  --res_sim_input                         true
% 7.34/1.49  --eq_ax_congr_red                       true
% 7.34/1.49  --pure_diseq_elim                       true
% 7.34/1.49  --brand_transform                       false
% 7.34/1.49  --non_eq_to_eq                          false
% 7.34/1.49  --prep_def_merge                        true
% 7.34/1.49  --prep_def_merge_prop_impl              false
% 7.34/1.49  --prep_def_merge_mbd                    true
% 7.34/1.49  --prep_def_merge_tr_red                 false
% 7.34/1.49  --prep_def_merge_tr_cl                  false
% 7.34/1.49  --smt_preprocessing                     true
% 7.34/1.49  --smt_ac_axioms                         fast
% 7.34/1.49  --preprocessed_out                      false
% 7.34/1.49  --preprocessed_stats                    false
% 7.34/1.49  
% 7.34/1.49  ------ Abstraction refinement Options
% 7.34/1.49  
% 7.34/1.49  --abstr_ref                             []
% 7.34/1.49  --abstr_ref_prep                        false
% 7.34/1.49  --abstr_ref_until_sat                   false
% 7.34/1.49  --abstr_ref_sig_restrict                funpre
% 7.34/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.34/1.49  --abstr_ref_under                       []
% 7.34/1.49  
% 7.34/1.49  ------ SAT Options
% 7.34/1.49  
% 7.34/1.49  --sat_mode                              false
% 7.34/1.49  --sat_fm_restart_options                ""
% 7.34/1.49  --sat_gr_def                            false
% 7.34/1.49  --sat_epr_types                         true
% 7.34/1.49  --sat_non_cyclic_types                  false
% 7.34/1.49  --sat_finite_models                     false
% 7.34/1.49  --sat_fm_lemmas                         false
% 7.34/1.49  --sat_fm_prep                           false
% 7.34/1.49  --sat_fm_uc_incr                        true
% 7.34/1.49  --sat_out_model                         small
% 7.34/1.49  --sat_out_clauses                       false
% 7.34/1.49  
% 7.34/1.49  ------ QBF Options
% 7.34/1.49  
% 7.34/1.49  --qbf_mode                              false
% 7.34/1.49  --qbf_elim_univ                         false
% 7.34/1.49  --qbf_dom_inst                          none
% 7.34/1.49  --qbf_dom_pre_inst                      false
% 7.34/1.49  --qbf_sk_in                             false
% 7.34/1.49  --qbf_pred_elim                         true
% 7.34/1.49  --qbf_split                             512
% 7.34/1.49  
% 7.34/1.49  ------ BMC1 Options
% 7.34/1.49  
% 7.34/1.49  --bmc1_incremental                      false
% 7.34/1.49  --bmc1_axioms                           reachable_all
% 7.34/1.49  --bmc1_min_bound                        0
% 7.34/1.49  --bmc1_max_bound                        -1
% 7.34/1.49  --bmc1_max_bound_default                -1
% 7.34/1.49  --bmc1_symbol_reachability              true
% 7.34/1.49  --bmc1_property_lemmas                  false
% 7.34/1.49  --bmc1_k_induction                      false
% 7.34/1.49  --bmc1_non_equiv_states                 false
% 7.34/1.49  --bmc1_deadlock                         false
% 7.34/1.49  --bmc1_ucm                              false
% 7.34/1.49  --bmc1_add_unsat_core                   none
% 7.34/1.49  --bmc1_unsat_core_children              false
% 7.34/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.34/1.49  --bmc1_out_stat                         full
% 7.34/1.49  --bmc1_ground_init                      false
% 7.34/1.49  --bmc1_pre_inst_next_state              false
% 7.34/1.49  --bmc1_pre_inst_state                   false
% 7.34/1.49  --bmc1_pre_inst_reach_state             false
% 7.34/1.49  --bmc1_out_unsat_core                   false
% 7.34/1.49  --bmc1_aig_witness_out                  false
% 7.34/1.49  --bmc1_verbose                          false
% 7.34/1.49  --bmc1_dump_clauses_tptp                false
% 7.34/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.34/1.49  --bmc1_dump_file                        -
% 7.34/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.34/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.34/1.49  --bmc1_ucm_extend_mode                  1
% 7.34/1.49  --bmc1_ucm_init_mode                    2
% 7.34/1.49  --bmc1_ucm_cone_mode                    none
% 7.34/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.34/1.49  --bmc1_ucm_relax_model                  4
% 7.34/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.34/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.34/1.49  --bmc1_ucm_layered_model                none
% 7.34/1.49  --bmc1_ucm_max_lemma_size               10
% 7.34/1.49  
% 7.34/1.49  ------ AIG Options
% 7.34/1.49  
% 7.34/1.49  --aig_mode                              false
% 7.34/1.49  
% 7.34/1.49  ------ Instantiation Options
% 7.34/1.49  
% 7.34/1.49  --instantiation_flag                    true
% 7.34/1.49  --inst_sos_flag                         false
% 7.34/1.49  --inst_sos_phase                        true
% 7.34/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.34/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.34/1.49  --inst_lit_sel_side                     num_symb
% 7.34/1.49  --inst_solver_per_active                1400
% 7.34/1.49  --inst_solver_calls_frac                1.
% 7.34/1.49  --inst_passive_queue_type               priority_queues
% 7.34/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.34/1.49  --inst_passive_queues_freq              [25;2]
% 7.34/1.49  --inst_dismatching                      true
% 7.34/1.49  --inst_eager_unprocessed_to_passive     true
% 7.34/1.49  --inst_prop_sim_given                   true
% 7.34/1.49  --inst_prop_sim_new                     false
% 7.34/1.49  --inst_subs_new                         false
% 7.34/1.49  --inst_eq_res_simp                      false
% 7.34/1.49  --inst_subs_given                       false
% 7.34/1.49  --inst_orphan_elimination               true
% 7.34/1.49  --inst_learning_loop_flag               true
% 7.34/1.49  --inst_learning_start                   3000
% 7.34/1.49  --inst_learning_factor                  2
% 7.34/1.49  --inst_start_prop_sim_after_learn       3
% 7.34/1.49  --inst_sel_renew                        solver
% 7.34/1.49  --inst_lit_activity_flag                true
% 7.34/1.49  --inst_restr_to_given                   false
% 7.34/1.49  --inst_activity_threshold               500
% 7.34/1.49  --inst_out_proof                        true
% 7.34/1.49  
% 7.34/1.49  ------ Resolution Options
% 7.34/1.49  
% 7.34/1.49  --resolution_flag                       true
% 7.34/1.49  --res_lit_sel                           adaptive
% 7.34/1.49  --res_lit_sel_side                      none
% 7.34/1.49  --res_ordering                          kbo
% 7.34/1.49  --res_to_prop_solver                    active
% 7.34/1.49  --res_prop_simpl_new                    false
% 7.34/1.49  --res_prop_simpl_given                  true
% 7.34/1.49  --res_passive_queue_type                priority_queues
% 7.34/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.34/1.49  --res_passive_queues_freq               [15;5]
% 7.34/1.49  --res_forward_subs                      full
% 7.34/1.49  --res_backward_subs                     full
% 7.34/1.49  --res_forward_subs_resolution           true
% 7.34/1.49  --res_backward_subs_resolution          true
% 7.34/1.49  --res_orphan_elimination                true
% 7.34/1.49  --res_time_limit                        2.
% 7.34/1.49  --res_out_proof                         true
% 7.34/1.49  
% 7.34/1.49  ------ Superposition Options
% 7.34/1.49  
% 7.34/1.49  --superposition_flag                    true
% 7.34/1.49  --sup_passive_queue_type                priority_queues
% 7.34/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.34/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.34/1.49  --demod_completeness_check              fast
% 7.34/1.49  --demod_use_ground                      true
% 7.34/1.49  --sup_to_prop_solver                    passive
% 7.34/1.49  --sup_prop_simpl_new                    true
% 7.34/1.49  --sup_prop_simpl_given                  true
% 7.34/1.49  --sup_fun_splitting                     false
% 7.34/1.49  --sup_smt_interval                      50000
% 7.34/1.49  
% 7.34/1.49  ------ Superposition Simplification Setup
% 7.34/1.49  
% 7.34/1.49  --sup_indices_passive                   []
% 7.34/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.34/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_full_bw                           [BwDemod]
% 7.34/1.49  --sup_immed_triv                        [TrivRules]
% 7.34/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.34/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_immed_bw_main                     []
% 7.34/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.34/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.49  
% 7.34/1.49  ------ Combination Options
% 7.34/1.49  
% 7.34/1.49  --comb_res_mult                         3
% 7.34/1.49  --comb_sup_mult                         2
% 7.34/1.49  --comb_inst_mult                        10
% 7.34/1.49  
% 7.34/1.49  ------ Debug Options
% 7.34/1.49  
% 7.34/1.49  --dbg_backtrace                         false
% 7.34/1.49  --dbg_dump_prop_clauses                 false
% 7.34/1.49  --dbg_dump_prop_clauses_file            -
% 7.34/1.49  --dbg_out_stat                          false
% 7.34/1.49  ------ Parsing...
% 7.34/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.34/1.49  ------ Proving...
% 7.34/1.49  ------ Problem Properties 
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  clauses                                 54
% 7.34/1.49  conjectures                             11
% 7.34/1.49  EPR                                     13
% 7.34/1.49  Horn                                    48
% 7.34/1.49  unary                                   24
% 7.34/1.49  binary                                  16
% 7.34/1.49  lits                                    134
% 7.34/1.49  lits eq                                 12
% 7.34/1.49  fd_pure                                 0
% 7.34/1.49  fd_pseudo                               0
% 7.34/1.49  fd_cond                                 3
% 7.34/1.49  fd_pseudo_cond                          2
% 7.34/1.49  AC symbols                              0
% 7.34/1.49  
% 7.34/1.49  ------ Schedule dynamic 5 is on 
% 7.34/1.49  
% 7.34/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  ------ 
% 7.34/1.49  Current options:
% 7.34/1.49  ------ 
% 7.34/1.49  
% 7.34/1.49  ------ Input Options
% 7.34/1.49  
% 7.34/1.49  --out_options                           all
% 7.34/1.49  --tptp_safe_out                         true
% 7.34/1.49  --problem_path                          ""
% 7.34/1.49  --include_path                          ""
% 7.34/1.49  --clausifier                            res/vclausify_rel
% 7.34/1.49  --clausifier_options                    --mode clausify
% 7.34/1.49  --stdin                                 false
% 7.34/1.49  --stats_out                             all
% 7.34/1.49  
% 7.34/1.49  ------ General Options
% 7.34/1.49  
% 7.34/1.49  --fof                                   false
% 7.34/1.49  --time_out_real                         305.
% 7.34/1.49  --time_out_virtual                      -1.
% 7.34/1.49  --symbol_type_check                     false
% 7.34/1.49  --clausify_out                          false
% 7.34/1.49  --sig_cnt_out                           false
% 7.34/1.49  --trig_cnt_out                          false
% 7.34/1.49  --trig_cnt_out_tolerance                1.
% 7.34/1.49  --trig_cnt_out_sk_spl                   false
% 7.34/1.49  --abstr_cl_out                          false
% 7.34/1.49  
% 7.34/1.49  ------ Global Options
% 7.34/1.49  
% 7.34/1.49  --schedule                              default
% 7.34/1.49  --add_important_lit                     false
% 7.34/1.49  --prop_solver_per_cl                    1000
% 7.34/1.49  --min_unsat_core                        false
% 7.34/1.49  --soft_assumptions                      false
% 7.34/1.49  --soft_lemma_size                       3
% 7.34/1.49  --prop_impl_unit_size                   0
% 7.34/1.49  --prop_impl_unit                        []
% 7.34/1.49  --share_sel_clauses                     true
% 7.34/1.49  --reset_solvers                         false
% 7.34/1.49  --bc_imp_inh                            [conj_cone]
% 7.34/1.49  --conj_cone_tolerance                   3.
% 7.34/1.49  --extra_neg_conj                        none
% 7.34/1.49  --large_theory_mode                     true
% 7.34/1.49  --prolific_symb_bound                   200
% 7.34/1.49  --lt_threshold                          2000
% 7.34/1.49  --clause_weak_htbl                      true
% 7.34/1.49  --gc_record_bc_elim                     false
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing Options
% 7.34/1.49  
% 7.34/1.49  --preprocessing_flag                    true
% 7.34/1.49  --time_out_prep_mult                    0.1
% 7.34/1.49  --splitting_mode                        input
% 7.34/1.49  --splitting_grd                         true
% 7.34/1.49  --splitting_cvd                         false
% 7.34/1.49  --splitting_cvd_svl                     false
% 7.34/1.49  --splitting_nvd                         32
% 7.34/1.49  --sub_typing                            true
% 7.34/1.49  --prep_gs_sim                           true
% 7.34/1.49  --prep_unflatten                        true
% 7.34/1.49  --prep_res_sim                          true
% 7.34/1.49  --prep_upred                            true
% 7.34/1.49  --prep_sem_filter                       exhaustive
% 7.34/1.49  --prep_sem_filter_out                   false
% 7.34/1.49  --pred_elim                             true
% 7.34/1.49  --res_sim_input                         true
% 7.34/1.49  --eq_ax_congr_red                       true
% 7.34/1.49  --pure_diseq_elim                       true
% 7.34/1.49  --brand_transform                       false
% 7.34/1.49  --non_eq_to_eq                          false
% 7.34/1.49  --prep_def_merge                        true
% 7.34/1.49  --prep_def_merge_prop_impl              false
% 7.34/1.49  --prep_def_merge_mbd                    true
% 7.34/1.49  --prep_def_merge_tr_red                 false
% 7.34/1.49  --prep_def_merge_tr_cl                  false
% 7.34/1.49  --smt_preprocessing                     true
% 7.34/1.49  --smt_ac_axioms                         fast
% 7.34/1.49  --preprocessed_out                      false
% 7.34/1.49  --preprocessed_stats                    false
% 7.34/1.49  
% 7.34/1.49  ------ Abstraction refinement Options
% 7.34/1.49  
% 7.34/1.49  --abstr_ref                             []
% 7.34/1.49  --abstr_ref_prep                        false
% 7.34/1.49  --abstr_ref_until_sat                   false
% 7.34/1.49  --abstr_ref_sig_restrict                funpre
% 7.34/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.34/1.49  --abstr_ref_under                       []
% 7.34/1.49  
% 7.34/1.49  ------ SAT Options
% 7.34/1.49  
% 7.34/1.49  --sat_mode                              false
% 7.34/1.49  --sat_fm_restart_options                ""
% 7.34/1.49  --sat_gr_def                            false
% 7.34/1.49  --sat_epr_types                         true
% 7.34/1.49  --sat_non_cyclic_types                  false
% 7.34/1.49  --sat_finite_models                     false
% 7.34/1.49  --sat_fm_lemmas                         false
% 7.34/1.49  --sat_fm_prep                           false
% 7.34/1.49  --sat_fm_uc_incr                        true
% 7.34/1.49  --sat_out_model                         small
% 7.34/1.49  --sat_out_clauses                       false
% 7.34/1.49  
% 7.34/1.49  ------ QBF Options
% 7.34/1.49  
% 7.34/1.49  --qbf_mode                              false
% 7.34/1.49  --qbf_elim_univ                         false
% 7.34/1.49  --qbf_dom_inst                          none
% 7.34/1.49  --qbf_dom_pre_inst                      false
% 7.34/1.49  --qbf_sk_in                             false
% 7.34/1.49  --qbf_pred_elim                         true
% 7.34/1.49  --qbf_split                             512
% 7.34/1.49  
% 7.34/1.49  ------ BMC1 Options
% 7.34/1.49  
% 7.34/1.49  --bmc1_incremental                      false
% 7.34/1.49  --bmc1_axioms                           reachable_all
% 7.34/1.49  --bmc1_min_bound                        0
% 7.34/1.49  --bmc1_max_bound                        -1
% 7.34/1.49  --bmc1_max_bound_default                -1
% 7.34/1.49  --bmc1_symbol_reachability              true
% 7.34/1.49  --bmc1_property_lemmas                  false
% 7.34/1.49  --bmc1_k_induction                      false
% 7.34/1.49  --bmc1_non_equiv_states                 false
% 7.34/1.49  --bmc1_deadlock                         false
% 7.34/1.49  --bmc1_ucm                              false
% 7.34/1.49  --bmc1_add_unsat_core                   none
% 7.34/1.49  --bmc1_unsat_core_children              false
% 7.34/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.34/1.49  --bmc1_out_stat                         full
% 7.34/1.49  --bmc1_ground_init                      false
% 7.34/1.49  --bmc1_pre_inst_next_state              false
% 7.34/1.49  --bmc1_pre_inst_state                   false
% 7.34/1.49  --bmc1_pre_inst_reach_state             false
% 7.34/1.49  --bmc1_out_unsat_core                   false
% 7.34/1.49  --bmc1_aig_witness_out                  false
% 7.34/1.49  --bmc1_verbose                          false
% 7.34/1.49  --bmc1_dump_clauses_tptp                false
% 7.34/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.34/1.49  --bmc1_dump_file                        -
% 7.34/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.34/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.34/1.49  --bmc1_ucm_extend_mode                  1
% 7.34/1.49  --bmc1_ucm_init_mode                    2
% 7.34/1.49  --bmc1_ucm_cone_mode                    none
% 7.34/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.34/1.49  --bmc1_ucm_relax_model                  4
% 7.34/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.34/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.34/1.49  --bmc1_ucm_layered_model                none
% 7.34/1.49  --bmc1_ucm_max_lemma_size               10
% 7.34/1.49  
% 7.34/1.49  ------ AIG Options
% 7.34/1.49  
% 7.34/1.49  --aig_mode                              false
% 7.34/1.49  
% 7.34/1.49  ------ Instantiation Options
% 7.34/1.49  
% 7.34/1.49  --instantiation_flag                    true
% 7.34/1.49  --inst_sos_flag                         false
% 7.34/1.49  --inst_sos_phase                        true
% 7.34/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.34/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.34/1.49  --inst_lit_sel_side                     none
% 7.34/1.49  --inst_solver_per_active                1400
% 7.34/1.49  --inst_solver_calls_frac                1.
% 7.34/1.49  --inst_passive_queue_type               priority_queues
% 7.34/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.34/1.49  --inst_passive_queues_freq              [25;2]
% 7.34/1.49  --inst_dismatching                      true
% 7.34/1.49  --inst_eager_unprocessed_to_passive     true
% 7.34/1.49  --inst_prop_sim_given                   true
% 7.34/1.49  --inst_prop_sim_new                     false
% 7.34/1.49  --inst_subs_new                         false
% 7.34/1.49  --inst_eq_res_simp                      false
% 7.34/1.49  --inst_subs_given                       false
% 7.34/1.49  --inst_orphan_elimination               true
% 7.34/1.49  --inst_learning_loop_flag               true
% 7.34/1.49  --inst_learning_start                   3000
% 7.34/1.49  --inst_learning_factor                  2
% 7.34/1.49  --inst_start_prop_sim_after_learn       3
% 7.34/1.49  --inst_sel_renew                        solver
% 7.34/1.49  --inst_lit_activity_flag                true
% 7.34/1.49  --inst_restr_to_given                   false
% 7.34/1.49  --inst_activity_threshold               500
% 7.34/1.49  --inst_out_proof                        true
% 7.34/1.49  
% 7.34/1.49  ------ Resolution Options
% 7.34/1.49  
% 7.34/1.49  --resolution_flag                       false
% 7.34/1.49  --res_lit_sel                           adaptive
% 7.34/1.49  --res_lit_sel_side                      none
% 7.34/1.49  --res_ordering                          kbo
% 7.34/1.49  --res_to_prop_solver                    active
% 7.34/1.49  --res_prop_simpl_new                    false
% 7.34/1.49  --res_prop_simpl_given                  true
% 7.34/1.49  --res_passive_queue_type                priority_queues
% 7.34/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.34/1.49  --res_passive_queues_freq               [15;5]
% 7.34/1.49  --res_forward_subs                      full
% 7.34/1.49  --res_backward_subs                     full
% 7.34/1.49  --res_forward_subs_resolution           true
% 7.34/1.49  --res_backward_subs_resolution          true
% 7.34/1.49  --res_orphan_elimination                true
% 7.34/1.49  --res_time_limit                        2.
% 7.34/1.49  --res_out_proof                         true
% 7.34/1.49  
% 7.34/1.49  ------ Superposition Options
% 7.34/1.49  
% 7.34/1.49  --superposition_flag                    true
% 7.34/1.49  --sup_passive_queue_type                priority_queues
% 7.34/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.34/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.34/1.49  --demod_completeness_check              fast
% 7.34/1.49  --demod_use_ground                      true
% 7.34/1.49  --sup_to_prop_solver                    passive
% 7.34/1.49  --sup_prop_simpl_new                    true
% 7.34/1.49  --sup_prop_simpl_given                  true
% 7.34/1.49  --sup_fun_splitting                     false
% 7.34/1.49  --sup_smt_interval                      50000
% 7.34/1.49  
% 7.34/1.49  ------ Superposition Simplification Setup
% 7.34/1.49  
% 7.34/1.49  --sup_indices_passive                   []
% 7.34/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.34/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_full_bw                           [BwDemod]
% 7.34/1.49  --sup_immed_triv                        [TrivRules]
% 7.34/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.34/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_immed_bw_main                     []
% 7.34/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.34/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.49  
% 7.34/1.49  ------ Combination Options
% 7.34/1.49  
% 7.34/1.49  --comb_res_mult                         3
% 7.34/1.49  --comb_sup_mult                         2
% 7.34/1.49  --comb_inst_mult                        10
% 7.34/1.49  
% 7.34/1.49  ------ Debug Options
% 7.34/1.49  
% 7.34/1.49  --dbg_backtrace                         false
% 7.34/1.49  --dbg_dump_prop_clauses                 false
% 7.34/1.49  --dbg_dump_prop_clauses_file            -
% 7.34/1.49  --dbg_out_stat                          false
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  ------ Proving...
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  % SZS status Theorem for theBenchmark.p
% 7.34/1.49  
% 7.34/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.34/1.49  
% 7.34/1.49  fof(f151,plain,(
% 7.34/1.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f31,conjecture,(
% 7.34/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f32,negated_conjecture,(
% 7.34/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.34/1.49    inference(negated_conjecture,[],[f31])).
% 7.34/1.49  
% 7.34/1.49  fof(f61,plain,(
% 7.34/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.34/1.49    inference(ennf_transformation,[],[f32])).
% 7.34/1.49  
% 7.34/1.49  fof(f62,plain,(
% 7.34/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.34/1.49    inference(flattening,[],[f61])).
% 7.34/1.49  
% 7.34/1.49  fof(f85,plain,(
% 7.34/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.34/1.49    inference(nnf_transformation,[],[f62])).
% 7.34/1.49  
% 7.34/1.49  fof(f86,plain,(
% 7.34/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.34/1.49    inference(flattening,[],[f85])).
% 7.34/1.49  
% 7.34/1.49  fof(f90,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK7 = X2 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK7))) )),
% 7.34/1.49    introduced(choice_axiom,[])).
% 7.34/1.49  
% 7.34/1.49  fof(f89,plain,(
% 7.34/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK6,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK6,X0,X1)) & sK6 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 7.34/1.49    introduced(choice_axiom,[])).
% 7.34/1.49  
% 7.34/1.49  fof(f88,plain,(
% 7.34/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(X2,X0,sK5)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(X2,X0,sK5)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK5)) & v1_funct_1(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))) )),
% 7.34/1.49    introduced(choice_axiom,[])).
% 7.34/1.49  
% 7.34/1.49  fof(f87,plain,(
% 7.34/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK4,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK4,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 7.34/1.49    introduced(choice_axiom,[])).
% 7.34/1.49  
% 7.34/1.49  fof(f91,plain,(
% 7.34/1.49    ((((~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)) & (v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)) & sK6 = sK7 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) & v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 7.34/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f86,f90,f89,f88,f87])).
% 7.34/1.49  
% 7.34/1.49  fof(f155,plain,(
% 7.34/1.49    sK6 = sK7),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f161,plain,(
% 7.34/1.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 7.34/1.49    inference(definition_unfolding,[],[f151,f155])).
% 7.34/1.49  
% 7.34/1.49  fof(f22,axiom,(
% 7.34/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f47,plain,(
% 7.34/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.34/1.49    inference(ennf_transformation,[],[f22])).
% 7.34/1.49  
% 7.34/1.49  fof(f48,plain,(
% 7.34/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.34/1.49    inference(flattening,[],[f47])).
% 7.34/1.49  
% 7.34/1.49  fof(f126,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f48])).
% 7.34/1.49  
% 7.34/1.49  fof(f23,axiom,(
% 7.34/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f49,plain,(
% 7.34/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.34/1.49    inference(ennf_transformation,[],[f23])).
% 7.34/1.49  
% 7.34/1.49  fof(f50,plain,(
% 7.34/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.34/1.49    inference(flattening,[],[f49])).
% 7.34/1.49  
% 7.34/1.49  fof(f80,plain,(
% 7.34/1.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.34/1.49    inference(nnf_transformation,[],[f50])).
% 7.34/1.49  
% 7.34/1.49  fof(f127,plain,(
% 7.34/1.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f80])).
% 7.34/1.49  
% 7.34/1.49  fof(f18,axiom,(
% 7.34/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f43,plain,(
% 7.34/1.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.34/1.49    inference(ennf_transformation,[],[f18])).
% 7.34/1.49  
% 7.34/1.49  fof(f120,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.34/1.49    inference(cnf_transformation,[],[f43])).
% 7.34/1.49  
% 7.34/1.49  fof(f17,axiom,(
% 7.34/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f42,plain,(
% 7.34/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.34/1.49    inference(ennf_transformation,[],[f17])).
% 7.34/1.49  
% 7.34/1.49  fof(f119,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.34/1.49    inference(cnf_transformation,[],[f42])).
% 7.34/1.49  
% 7.34/1.49  fof(f149,plain,(
% 7.34/1.49    v1_funct_1(sK6)),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f163,plain,(
% 7.34/1.49    v1_funct_1(sK7)),
% 7.34/1.49    inference(definition_unfolding,[],[f149,f155])).
% 7.34/1.49  
% 7.34/1.49  fof(f150,plain,(
% 7.34/1.49    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f162,plain,(
% 7.34/1.49    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5))),
% 7.34/1.49    inference(definition_unfolding,[],[f150,f155])).
% 7.34/1.49  
% 7.34/1.49  fof(f4,axiom,(
% 7.34/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f36,plain,(
% 7.34/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.34/1.49    inference(ennf_transformation,[],[f4])).
% 7.34/1.49  
% 7.34/1.49  fof(f98,plain,(
% 7.34/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f36])).
% 7.34/1.49  
% 7.34/1.49  fof(f29,axiom,(
% 7.34/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f57,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.34/1.49    inference(ennf_transformation,[],[f29])).
% 7.34/1.49  
% 7.34/1.49  fof(f58,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.34/1.49    inference(flattening,[],[f57])).
% 7.34/1.49  
% 7.34/1.49  fof(f83,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.34/1.49    inference(nnf_transformation,[],[f58])).
% 7.34/1.49  
% 7.34/1.49  fof(f141,plain,(
% 7.34/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f83])).
% 7.34/1.49  
% 7.34/1.49  fof(f170,plain,(
% 7.34/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.34/1.49    inference(equality_resolution,[],[f141])).
% 7.34/1.49  
% 7.34/1.49  fof(f8,axiom,(
% 7.34/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f75,plain,(
% 7.34/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.34/1.49    inference(nnf_transformation,[],[f8])).
% 7.34/1.49  
% 7.34/1.49  fof(f76,plain,(
% 7.34/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.34/1.49    inference(flattening,[],[f75])).
% 7.34/1.49  
% 7.34/1.49  fof(f106,plain,(
% 7.34/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.34/1.49    inference(cnf_transformation,[],[f76])).
% 7.34/1.49  
% 7.34/1.49  fof(f166,plain,(
% 7.34/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.34/1.49    inference(equality_resolution,[],[f106])).
% 7.34/1.49  
% 7.34/1.49  fof(f154,plain,(
% 7.34/1.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f121,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.34/1.49    inference(cnf_transformation,[],[f43])).
% 7.34/1.49  
% 7.34/1.49  fof(f14,axiom,(
% 7.34/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f40,plain,(
% 7.34/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.34/1.49    inference(ennf_transformation,[],[f14])).
% 7.34/1.49  
% 7.34/1.49  fof(f79,plain,(
% 7.34/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.34/1.49    inference(nnf_transformation,[],[f40])).
% 7.34/1.49  
% 7.34/1.49  fof(f114,plain,(
% 7.34/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f79])).
% 7.34/1.49  
% 7.34/1.49  fof(f25,axiom,(
% 7.34/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f51,plain,(
% 7.34/1.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.34/1.49    inference(ennf_transformation,[],[f25])).
% 7.34/1.49  
% 7.34/1.49  fof(f52,plain,(
% 7.34/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.34/1.49    inference(flattening,[],[f51])).
% 7.34/1.49  
% 7.34/1.49  fof(f136,plain,(
% 7.34/1.49    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f52])).
% 7.34/1.49  
% 7.34/1.49  fof(f153,plain,(
% 7.34/1.49    v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f30,axiom,(
% 7.34/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f59,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.34/1.49    inference(ennf_transformation,[],[f30])).
% 7.34/1.49  
% 7.34/1.49  fof(f60,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.34/1.49    inference(flattening,[],[f59])).
% 7.34/1.49  
% 7.34/1.49  fof(f84,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.34/1.49    inference(nnf_transformation,[],[f60])).
% 7.34/1.49  
% 7.34/1.49  fof(f143,plain,(
% 7.34/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f84])).
% 7.34/1.49  
% 7.34/1.49  fof(f172,plain,(
% 7.34/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.34/1.49    inference(equality_resolution,[],[f143])).
% 7.34/1.49  
% 7.34/1.49  fof(f145,plain,(
% 7.34/1.49    v2_pre_topc(sK4)),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f146,plain,(
% 7.34/1.49    l1_pre_topc(sK4)),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f147,plain,(
% 7.34/1.49    v2_pre_topc(sK5)),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f148,plain,(
% 7.34/1.49    l1_pre_topc(sK5)),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f157,plain,(
% 7.34/1.49    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK6,sK4,sK5)),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f159,plain,(
% 7.34/1.49    ~v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~v5_pre_topc(sK7,sK4,sK5)),
% 7.34/1.49    inference(definition_unfolding,[],[f157,f155])).
% 7.34/1.49  
% 7.34/1.49  fof(f28,axiom,(
% 7.34/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f33,plain,(
% 7.34/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.34/1.49    inference(pure_predicate_removal,[],[f28])).
% 7.34/1.49  
% 7.34/1.49  fof(f55,plain,(
% 7.34/1.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.34/1.49    inference(ennf_transformation,[],[f33])).
% 7.34/1.49  
% 7.34/1.49  fof(f56,plain,(
% 7.34/1.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.34/1.49    inference(flattening,[],[f55])).
% 7.34/1.49  
% 7.34/1.49  fof(f140,plain,(
% 7.34/1.49    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f56])).
% 7.34/1.49  
% 7.34/1.49  fof(f27,axiom,(
% 7.34/1.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f54,plain,(
% 7.34/1.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.34/1.49    inference(ennf_transformation,[],[f27])).
% 7.34/1.49  
% 7.34/1.49  fof(f139,plain,(
% 7.34/1.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f54])).
% 7.34/1.49  
% 7.34/1.49  fof(f26,axiom,(
% 7.34/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f34,plain,(
% 7.34/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.34/1.49    inference(pure_predicate_removal,[],[f26])).
% 7.34/1.49  
% 7.34/1.49  fof(f53,plain,(
% 7.34/1.49    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.34/1.49    inference(ennf_transformation,[],[f34])).
% 7.34/1.49  
% 7.34/1.49  fof(f138,plain,(
% 7.34/1.49    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.34/1.49    inference(cnf_transformation,[],[f53])).
% 7.34/1.49  
% 7.34/1.49  fof(f13,axiom,(
% 7.34/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f39,plain,(
% 7.34/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.34/1.49    inference(ennf_transformation,[],[f13])).
% 7.34/1.49  
% 7.34/1.49  fof(f78,plain,(
% 7.34/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.34/1.49    inference(nnf_transformation,[],[f39])).
% 7.34/1.49  
% 7.34/1.49  fof(f112,plain,(
% 7.34/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f78])).
% 7.34/1.49  
% 7.34/1.49  fof(f142,plain,(
% 7.34/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f83])).
% 7.34/1.49  
% 7.34/1.49  fof(f169,plain,(
% 7.34/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.34/1.49    inference(equality_resolution,[],[f142])).
% 7.34/1.49  
% 7.34/1.49  fof(f20,axiom,(
% 7.34/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f45,plain,(
% 7.34/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.34/1.49    inference(ennf_transformation,[],[f20])).
% 7.34/1.49  
% 7.34/1.49  fof(f46,plain,(
% 7.34/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 7.34/1.49    inference(flattening,[],[f45])).
% 7.34/1.49  
% 7.34/1.49  fof(f123,plain,(
% 7.34/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 7.34/1.49    inference(cnf_transformation,[],[f46])).
% 7.34/1.49  
% 7.34/1.49  fof(f11,axiom,(
% 7.34/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f77,plain,(
% 7.34/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.34/1.49    inference(nnf_transformation,[],[f11])).
% 7.34/1.49  
% 7.34/1.49  fof(f109,plain,(
% 7.34/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.34/1.49    inference(cnf_transformation,[],[f77])).
% 7.34/1.49  
% 7.34/1.49  fof(f6,axiom,(
% 7.34/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f73,plain,(
% 7.34/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.34/1.49    inference(nnf_transformation,[],[f6])).
% 7.34/1.49  
% 7.34/1.49  fof(f74,plain,(
% 7.34/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.34/1.49    inference(flattening,[],[f73])).
% 7.34/1.49  
% 7.34/1.49  fof(f102,plain,(
% 7.34/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f74])).
% 7.34/1.49  
% 7.34/1.49  fof(f21,axiom,(
% 7.34/1.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f124,plain,(
% 7.34/1.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.34/1.49    inference(cnf_transformation,[],[f21])).
% 7.34/1.49  
% 7.34/1.49  fof(f15,axiom,(
% 7.34/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.34/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f116,plain,(
% 7.34/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.34/1.49    inference(cnf_transformation,[],[f15])).
% 7.34/1.49  
% 7.34/1.49  fof(f144,plain,(
% 7.34/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f84])).
% 7.34/1.49  
% 7.34/1.49  fof(f171,plain,(
% 7.34/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.34/1.49    inference(equality_resolution,[],[f144])).
% 7.34/1.49  
% 7.34/1.49  fof(f156,plain,(
% 7.34/1.49    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK6,sK4,sK5)),
% 7.34/1.49    inference(cnf_transformation,[],[f91])).
% 7.34/1.49  
% 7.34/1.49  fof(f160,plain,(
% 7.34/1.49    v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | v5_pre_topc(sK7,sK4,sK5)),
% 7.34/1.49    inference(definition_unfolding,[],[f156,f155])).
% 7.34/1.49  
% 7.34/1.49  cnf(c_57,negated_conjecture,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
% 7.34/1.49      inference(cnf_transformation,[],[f161]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3497,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_32,plain,
% 7.34/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.34/1.49      | v1_partfun1(X0,X1)
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.49      | ~ v1_funct_1(X0)
% 7.34/1.49      | v1_xboole_0(X2) ),
% 7.34/1.49      inference(cnf_transformation,[],[f126]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_35,plain,
% 7.34/1.49      ( ~ v1_partfun1(X0,X1)
% 7.34/1.49      | ~ v4_relat_1(X0,X1)
% 7.34/1.49      | ~ v1_relat_1(X0)
% 7.34/1.49      | k1_relat_1(X0) = X1 ),
% 7.34/1.49      inference(cnf_transformation,[],[f127]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_776,plain,
% 7.34/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.34/1.49      | ~ v4_relat_1(X0,X1)
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.49      | ~ v1_funct_1(X0)
% 7.34/1.49      | ~ v1_relat_1(X0)
% 7.34/1.49      | v1_xboole_0(X2)
% 7.34/1.49      | k1_relat_1(X0) = X1 ),
% 7.34/1.49      inference(resolution,[status(thm)],[c_32,c_35]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_28,plain,
% 7.34/1.49      ( v4_relat_1(X0,X1)
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.34/1.49      inference(cnf_transformation,[],[f120]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_26,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.49      | v1_relat_1(X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f119]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_780,plain,
% 7.34/1.49      ( ~ v1_funct_1(X0)
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.34/1.49      | v1_xboole_0(X2)
% 7.34/1.49      | k1_relat_1(X0) = X1 ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_776,c_28,c_26]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_781,plain,
% 7.34/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.49      | ~ v1_funct_1(X0)
% 7.34/1.49      | v1_xboole_0(X2)
% 7.34/1.49      | k1_relat_1(X0) = X1 ),
% 7.34/1.49      inference(renaming,[status(thm)],[c_780]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3488,plain,
% 7.34/1.49      ( k1_relat_1(X0) = X1
% 7.34/1.49      | v1_funct_2(X0,X1,X2) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.34/1.49      | v1_funct_1(X0) != iProver_top
% 7.34/1.49      | v1_xboole_0(X2) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6518,plain,
% 7.34/1.49      ( u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top
% 7.34/1.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3497,c_3488]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_59,negated_conjecture,
% 7.34/1.49      ( v1_funct_1(sK7) ),
% 7.34/1.49      inference(cnf_transformation,[],[f163]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_68,plain,
% 7.34/1.49      ( v1_funct_1(sK7) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_58,negated_conjecture,
% 7.34/1.49      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) ),
% 7.34/1.49      inference(cnf_transformation,[],[f162]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_69,plain,
% 7.34/1.49      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6979,plain,
% 7.34/1.49      ( u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_6518,c_68,c_69]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6,plain,
% 7.34/1.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.34/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3527,plain,
% 7.34/1.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6985,plain,
% 7.34/1.49      ( u1_struct_0(sK5) = k1_xboole_0
% 7.34/1.49      | u1_struct_0(sK4) = k1_relat_1(sK7) ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6979,c_3527]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_49,plain,
% 7.34/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.34/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.34/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.34/1.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.34/1.49      | ~ v2_pre_topc(X1)
% 7.34/1.49      | ~ v2_pre_topc(X2)
% 7.34/1.49      | ~ l1_pre_topc(X1)
% 7.34/1.49      | ~ l1_pre_topc(X2)
% 7.34/1.49      | ~ v1_funct_1(X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f170]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3505,plain,
% 7.34/1.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.34/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.34/1.49      | v2_pre_topc(X1) != iProver_top
% 7.34/1.49      | v2_pre_topc(X2) != iProver_top
% 7.34/1.49      | l1_pre_topc(X1) != iProver_top
% 7.34/1.49      | l1_pre_topc(X2) != iProver_top
% 7.34/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_11288,plain,
% 7.34/1.49      ( u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | v5_pre_topc(X0,X1,sK5) != iProver_top
% 7.34/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK5) = iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_xboole_0))) != iProver_top
% 7.34/1.49      | v2_pre_topc(X1) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(X1) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top
% 7.34/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6985,c_3505]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_12,plain,
% 7.34/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.34/1.49      inference(cnf_transformation,[],[f166]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_11327,plain,
% 7.34/1.49      ( u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | v5_pre_topc(X0,X1,sK5) != iProver_top
% 7.34/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK5) = iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.34/1.49      | v2_pre_topc(X1) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(X1) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top
% 7.34/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.34/1.49      inference(demodulation,[status(thm)],[c_11288,c_12]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_70,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_54,negated_conjecture,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) ),
% 7.34/1.49      inference(cnf_transformation,[],[f154]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_73,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3936,plain,
% 7.34/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
% 7.34/1.49      | v1_relat_1(sK7) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_26]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3937,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
% 7.34/1.49      | v1_relat_1(sK7) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_3936]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_27,plain,
% 7.34/1.49      ( v5_relat_1(X0,X1)
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.34/1.49      inference(cnf_transformation,[],[f121]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_22,plain,
% 7.34/1.49      ( ~ v5_relat_1(X0,X1)
% 7.34/1.49      | r1_tarski(k2_relat_1(X0),X1)
% 7.34/1.49      | ~ v1_relat_1(X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f114]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_738,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.49      | r1_tarski(k2_relat_1(X0),X2)
% 7.34/1.49      | ~ v1_relat_1(X0) ),
% 7.34/1.49      inference(resolution,[status(thm)],[c_27,c_22]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_742,plain,
% 7.34/1.49      ( r1_tarski(k2_relat_1(X0),X2)
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_738,c_26]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_743,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.49      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.34/1.49      inference(renaming,[status(thm)],[c_742]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3989,plain,
% 7.34/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 7.34/1.49      | r1_tarski(k2_relat_1(sK7),u1_struct_0(sK5)) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_743]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3990,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | r1_tarski(k2_relat_1(sK7),u1_struct_0(sK5)) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_3989]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_43,plain,
% 7.34/1.49      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.34/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.34/1.49      | ~ v1_funct_1(X0)
% 7.34/1.49      | ~ v1_relat_1(X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f136]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4016,plain,
% 7.34/1.49      ( v1_funct_2(sK7,k1_relat_1(sK7),X0)
% 7.34/1.49      | ~ r1_tarski(k2_relat_1(sK7),X0)
% 7.34/1.49      | ~ v1_funct_1(sK7)
% 7.34/1.49      | ~ v1_relat_1(sK7) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_43]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4244,plain,
% 7.34/1.49      ( v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(sK5))
% 7.34/1.49      | ~ r1_tarski(k2_relat_1(sK7),u1_struct_0(sK5))
% 7.34/1.49      | ~ v1_funct_1(sK7)
% 7.34/1.49      | ~ v1_relat_1(sK7) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_4016]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4245,plain,
% 7.34/1.49      ( v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(sK5)) = iProver_top
% 7.34/1.49      | r1_tarski(k2_relat_1(sK7),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top
% 7.34/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_4244]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3500,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6517,plain,
% 7.34/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top
% 7.34/1.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3500,c_3488]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_55,negated_conjecture,
% 7.34/1.49      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
% 7.34/1.49      inference(cnf_transformation,[],[f153]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_72,plain,
% 7.34/1.49      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6987,plain,
% 7.34/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
% 7.34/1.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_6517,c_68,c_72]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6993,plain,
% 7.34/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 7.34/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7) ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6987,c_3527]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3499,plain,
% 7.34/1.49      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_9641,plain,
% 7.34/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0) = iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6993,c_3499]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_51,plain,
% 7.34/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.34/1.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.34/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.34/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.34/1.49      | ~ v2_pre_topc(X1)
% 7.34/1.49      | ~ v2_pre_topc(X2)
% 7.34/1.49      | ~ l1_pre_topc(X1)
% 7.34/1.49      | ~ l1_pre_topc(X2)
% 7.34/1.49      | ~ v1_funct_1(X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f172]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3503,plain,
% 7.34/1.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.34/1.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.34/1.49      | v2_pre_topc(X1) != iProver_top
% 7.34/1.49      | v2_pre_topc(X2) != iProver_top
% 7.34/1.49      | l1_pre_topc(X1) != iProver_top
% 7.34/1.49      | l1_pre_topc(X2) != iProver_top
% 7.34/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_8882,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3500,c_3503]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_63,negated_conjecture,
% 7.34/1.49      ( v2_pre_topc(sK4) ),
% 7.34/1.49      inference(cnf_transformation,[],[f145]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_64,plain,
% 7.34/1.49      ( v2_pre_topc(sK4) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_62,negated_conjecture,
% 7.34/1.49      ( l1_pre_topc(sK4) ),
% 7.34/1.49      inference(cnf_transformation,[],[f146]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_65,plain,
% 7.34/1.49      ( l1_pre_topc(sK4) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_61,negated_conjecture,
% 7.34/1.49      ( v2_pre_topc(sK5) ),
% 7.34/1.49      inference(cnf_transformation,[],[f147]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_66,plain,
% 7.34/1.49      ( v2_pre_topc(sK5) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_60,negated_conjecture,
% 7.34/1.49      ( l1_pre_topc(sK5) ),
% 7.34/1.49      inference(cnf_transformation,[],[f148]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_67,plain,
% 7.34/1.49      ( l1_pre_topc(sK5) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_52,negated_conjecture,
% 7.34/1.49      ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 7.34/1.49      | ~ v5_pre_topc(sK7,sK4,sK5) ),
% 7.34/1.49      inference(cnf_transformation,[],[f159]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_75,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,sK4,sK5) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_47,plain,
% 7.34/1.49      ( ~ v2_pre_topc(X0)
% 7.34/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.34/1.49      | ~ l1_pre_topc(X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f140]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_88,plain,
% 7.34/1.49      ( v2_pre_topc(X0) != iProver_top
% 7.34/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 7.34/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_90,plain,
% 7.34/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 7.34/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_88]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_46,plain,
% 7.34/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.34/1.49      | ~ l1_pre_topc(X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f139]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_91,plain,
% 7.34/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.34/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_93,plain,
% 7.34/1.49      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
% 7.34/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_91]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_45,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.34/1.49      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.34/1.49      inference(cnf_transformation,[],[f138]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3958,plain,
% 7.34/1.49      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.34/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_45]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3959,plain,
% 7.34/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 7.34/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_3958]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3961,plain,
% 7.34/1.49      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 7.34/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_3959]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_20,plain,
% 7.34/1.49      ( ~ v4_relat_1(X0,X1)
% 7.34/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.34/1.49      | ~ v1_relat_1(X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f112]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_810,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.34/1.49      | ~ v1_relat_1(X0) ),
% 7.34/1.49      inference(resolution,[status(thm)],[c_28,c_20]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_814,plain,
% 7.34/1.49      ( r1_tarski(k1_relat_1(X0),X1)
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_810,c_26]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_815,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.49      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.34/1.49      inference(renaming,[status(thm)],[c_814]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4001,plain,
% 7.34/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_815]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4002,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_4001]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_48,plain,
% 7.34/1.49      ( v5_pre_topc(X0,X1,X2)
% 7.34/1.49      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.34/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.34/1.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.34/1.49      | ~ v2_pre_topc(X1)
% 7.34/1.49      | ~ v2_pre_topc(X2)
% 7.34/1.49      | ~ l1_pre_topc(X1)
% 7.34/1.49      | ~ l1_pre_topc(X2)
% 7.34/1.49      | ~ v1_funct_1(X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f169]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4078,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,X0,X1)
% 7.34/1.49      | ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.34/1.49      | ~ v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
% 7.34/1.49      | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
% 7.34/1.49      | ~ v2_pre_topc(X0)
% 7.34/1.49      | ~ v2_pre_topc(X1)
% 7.34/1.49      | ~ l1_pre_topc(X0)
% 7.34/1.49      | ~ l1_pre_topc(X1)
% 7.34/1.49      | ~ v1_funct_1(sK7) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_48]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4296,plain,
% 7.34/1.49      ( ~ v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5)
% 7.34/1.49      | v5_pre_topc(sK7,sK4,sK5)
% 7.34/1.49      | ~ v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))
% 7.34/1.49      | ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 7.34/1.49      | ~ v2_pre_topc(sK5)
% 7.34/1.49      | ~ v2_pre_topc(sK4)
% 7.34/1.49      | ~ l1_pre_topc(sK5)
% 7.34/1.49      | ~ l1_pre_topc(sK4)
% 7.34/1.49      | ~ v1_funct_1(sK7) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_4078]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4297,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,sK4,sK5) = iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK4) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_4296]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_30,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.34/1.49      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 7.34/1.49      inference(cnf_transformation,[],[f123]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4167,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK5))))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 7.34/1.49      | ~ r1_tarski(k1_relat_1(sK7),X0) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_30]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4364,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5))))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 7.34/1.49      | ~ r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_4167]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4365,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) = iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_4364]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_9360,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_8882,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_72,c_73,
% 7.34/1.49                 c_75,c_90,c_93,c_3961,c_4002,c_4297,c_4365]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_9366,plain,
% 7.34/1.49      ( u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_xboole_0) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6985,c_9360]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_9980,plain,
% 7.34/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
% 7.34/1.49      | u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_9641,c_9366]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3496,plain,
% 7.34/1.49      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_8437,plain,
% 7.34/1.49      ( u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),k1_xboole_0) = iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6985,c_3496]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_17,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.34/1.49      inference(cnf_transformation,[],[f109]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3521,plain,
% 7.34/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.34/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6593,plain,
% 7.34/1.49      ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))) = iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3497,c_3521]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_8,plain,
% 7.34/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.34/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3525,plain,
% 7.34/1.49      ( X0 = X1
% 7.34/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.34/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_11717,plain,
% 7.34/1.49      ( k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK7
% 7.34/1.49      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)),sK7) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6593,c_3525]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_12599,plain,
% 7.34/1.49      ( k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK7
% 7.34/1.49      | u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK4),k1_xboole_0),sK7) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6985,c_11717]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_12600,plain,
% 7.34/1.49      ( k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK7
% 7.34/1.49      | u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
% 7.34/1.49      inference(demodulation,[status(thm)],[c_12599,c_12]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_31,plain,
% 7.34/1.49      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.34/1.49      inference(cnf_transformation,[],[f124]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3516,plain,
% 7.34/1.49      ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_5104,plain,
% 7.34/1.49      ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_12,c_3516]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3487,plain,
% 7.34/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_5373,plain,
% 7.34/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_12,c_3487]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_8044,plain,
% 7.34/1.49      ( r1_tarski(k1_relat_1(k6_relat_1(k1_xboole_0)),X0) = iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_5104,c_5373]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_24,plain,
% 7.34/1.49      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.34/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_8052,plain,
% 7.34/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.34/1.49      inference(demodulation,[status(thm)],[c_8044,c_24]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_13327,plain,
% 7.34/1.49      ( k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)) = sK7
% 7.34/1.49      | u1_struct_0(sK4) = k1_relat_1(sK7) ),
% 7.34/1.49      inference(forward_subsumption_resolution,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_12600,c_8052]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_13328,plain,
% 7.34/1.49      ( k2_zfmisc_1(u1_struct_0(sK4),k1_xboole_0) = sK7
% 7.34/1.49      | u1_struct_0(sK4) = k1_relat_1(sK7) ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6985,c_13327]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_13393,plain,
% 7.34/1.49      ( u1_struct_0(sK4) = k1_relat_1(sK7) | sK7 = k1_xboole_0 ),
% 7.34/1.49      inference(demodulation,[status(thm)],[c_13328,c_12]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3506,plain,
% 7.34/1.49      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.34/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.34/1.49      | v2_pre_topc(X1) != iProver_top
% 7.34/1.49      | v2_pre_topc(X2) != iProver_top
% 7.34/1.49      | l1_pre_topc(X1) != iProver_top
% 7.34/1.49      | l1_pre_topc(X2) != iProver_top
% 7.34/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_12695,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
% 7.34/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.34/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK4) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3500,c_3506]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4004,plain,
% 7.34/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),u1_struct_0(sK4)) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_815]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4005,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),u1_struct_0(sK4)) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_4004]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4334,plain,
% 7.34/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 7.34/1.49      | ~ v2_pre_topc(sK5)
% 7.34/1.49      | ~ l1_pre_topc(sK5) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_47]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4335,plain,
% 7.34/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_4334]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4162,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
% 7.34/1.49      | ~ r1_tarski(k1_relat_1(sK7),X0) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_30]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4349,plain,
% 7.34/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
% 7.34/1.49      | ~ r1_tarski(k1_relat_1(sK7),u1_struct_0(sK4)) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_4162]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4350,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),u1_struct_0(sK4)) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_4349]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_5312,plain,
% 7.34/1.49      ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 7.34/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_3958]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_5313,plain,
% 7.34/1.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_5312]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_7885,plain,
% 7.34/1.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 7.34/1.49      | ~ l1_pre_topc(sK5) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_46]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_7886,plain,
% 7.34/1.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_7885]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_11282,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
% 7.34/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.34/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK4) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3500,c_3505]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_50,plain,
% 7.34/1.49      ( v5_pre_topc(X0,X1,X2)
% 7.34/1.49      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.34/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.34/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.34/1.49      | ~ v2_pre_topc(X1)
% 7.34/1.49      | ~ v2_pre_topc(X2)
% 7.34/1.49      | ~ l1_pre_topc(X1)
% 7.34/1.49      | ~ l1_pre_topc(X2)
% 7.34/1.49      | ~ v1_funct_1(X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f171]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4096,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,X0,X1)
% 7.34/1.49      | ~ v5_pre_topc(sK7,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.34/1.49      | ~ v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
% 7.34/1.49      | ~ v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 7.34/1.49      | ~ v2_pre_topc(X0)
% 7.34/1.49      | ~ v2_pre_topc(X1)
% 7.34/1.49      | ~ l1_pre_topc(X0)
% 7.34/1.49      | ~ l1_pre_topc(X1)
% 7.34/1.49      | ~ v1_funct_1(sK7) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_50]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4373,plain,
% 7.34/1.49      ( ~ v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 7.34/1.49      | v5_pre_topc(sK7,sK4,sK5)
% 7.34/1.49      | ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
% 7.34/1.49      | ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
% 7.34/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
% 7.34/1.49      | ~ v2_pre_topc(sK5)
% 7.34/1.49      | ~ v2_pre_topc(sK4)
% 7.34/1.49      | ~ l1_pre_topc(sK5)
% 7.34/1.49      | ~ l1_pre_topc(sK4)
% 7.34/1.49      | ~ v1_funct_1(sK7) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_4096]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4374,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,sK4,sK5) = iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK4) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_4373]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_12107,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_11282,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_72,c_73,
% 7.34/1.49                 c_75,c_4005,c_4335,c_4350,c_4374,c_5313,c_7886]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_14486,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_12695,c_64,c_65,c_66,c_67,c_68,c_70,c_72,c_73,c_4005,
% 7.34/1.49                 c_4335,c_4350,c_5313,c_7886,c_12107]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_14493,plain,
% 7.34/1.49      ( sK7 = k1_xboole_0
% 7.34/1.49      | v5_pre_topc(sK7,g1_pre_topc(k1_relat_1(sK7),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_13393,c_14486]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_53,negated_conjecture,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 7.34/1.49      | v5_pre_topc(sK7,sK4,sK5) ),
% 7.34/1.49      inference(cnf_transformation,[],[f160]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3501,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,sK4,sK5) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_14492,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,sK4,sK5) = iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3501,c_14486]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3517,plain,
% 7.34/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_15324,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3500,c_3517]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_16031,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,X0,sK5) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),u1_struct_0(X0)) != iProver_top
% 7.34/1.49      | v2_pre_topc(X0) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(X0) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_15324,c_3503]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_16150,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,sK4,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,sK4,sK5) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),u1_struct_0(sK4)) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK4) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_16031]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_19355,plain,
% 7.34/1.49      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_14493,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_4005,
% 7.34/1.49                 c_12107,c_14492,c_16150]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_19361,plain,
% 7.34/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),k1_xboole_0) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6993,c_19355]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_21533,plain,
% 7.34/1.49      ( u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7) ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_9980,c_9754,c_19129]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_21534,plain,
% 7.34/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = k1_relat_1(sK7)
% 7.34/1.49      | u1_struct_0(sK4) = k1_relat_1(sK7) ),
% 7.34/1.49      inference(renaming,[status(thm)],[c_21533]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3504,plain,
% 7.34/1.49      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.34/1.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.34/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.34/1.49      | v2_pre_topc(X1) != iProver_top
% 7.34/1.49      | v2_pre_topc(X2) != iProver_top
% 7.34/1.49      | l1_pre_topc(X1) != iProver_top
% 7.34/1.49      | l1_pre_topc(X2) != iProver_top
% 7.34/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_9998,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3500,c_3504]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_10826,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_9998,c_64,c_65,c_66,c_67,c_68,c_70,c_72,c_73,c_90,
% 7.34/1.49                 c_93,c_3961,c_4002,c_4365,c_9360]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_13434,plain,
% 7.34/1.49      ( sK7 = k1_xboole_0
% 7.34/1.49      | v5_pre_topc(sK7,g1_pre_topc(k1_relat_1(sK7),u1_pre_topc(sK4)),g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_13393,c_10826]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_10832,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,sK4,sK5) = iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3501,c_10826]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_15325,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK5)))) = iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_3497,c_3517]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_15737,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,X0,sK5) != iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK5) = iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 7.34/1.49      | v2_pre_topc(X0) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(X0) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_15325,c_3505]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_15816,plain,
% 7.34/1.49      ( v5_pre_topc(sK7,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)),sK5) = iProver_top
% 7.34/1.49      | v5_pre_topc(sK7,sK4,sK5) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) != iProver_top
% 7.34/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) != iProver_top
% 7.34/1.49      | r1_tarski(k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK5) != iProver_top
% 7.34/1.49      | v2_pre_topc(sK4) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK5) != iProver_top
% 7.34/1.49      | l1_pre_topc(sK4) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_15737]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_19113,plain,
% 7.34/1.49      ( v1_funct_2(sK7,u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(sK5)) != iProver_top ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_13434,c_64,c_65,c_66,c_67,c_68,c_69,c_70,c_73,c_4002,
% 7.34/1.49                 c_9360,c_10832,c_15816]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_21568,plain,
% 7.34/1.49      ( u1_struct_0(sK4) = k1_relat_1(sK7)
% 7.34/1.49      | v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(sK5)) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_21534,c_19113]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_22217,plain,
% 7.34/1.49      ( u1_struct_0(sK4) = k1_relat_1(sK7) ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_11327,c_68,c_70,c_73,c_3937,c_3990,c_4245,c_21568]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_22223,plain,
% 7.34/1.49      ( v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
% 7.34/1.49      inference(demodulation,[status(thm)],[c_22217,c_19355]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4241,plain,
% 7.34/1.49      ( v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
% 7.34/1.49      | ~ r1_tarski(k2_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))
% 7.34/1.49      | ~ v1_funct_1(sK7)
% 7.34/1.49      | ~ v1_relat_1(sK7) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_4016]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4242,plain,
% 7.34/1.49      ( v1_funct_2(sK7,k1_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 7.34/1.49      | r1_tarski(k2_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
% 7.34/1.49      | v1_funct_1(sK7) != iProver_top
% 7.34/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_4241]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3986,plain,
% 7.34/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
% 7.34/1.49      | r1_tarski(k2_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_743]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_3987,plain,
% 7.34/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
% 7.34/1.49      | r1_tarski(k2_relat_1(sK7),u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_3986]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(contradiction,plain,
% 7.34/1.49      ( $false ),
% 7.34/1.49      inference(minisat,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_22223,c_4242,c_3987,c_3937,c_73,c_68]) ).
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.34/1.49  
% 7.34/1.49  ------                               Statistics
% 7.34/1.49  
% 7.34/1.49  ------ General
% 7.34/1.49  
% 7.34/1.49  abstr_ref_over_cycles:                  0
% 7.34/1.49  abstr_ref_under_cycles:                 0
% 7.34/1.49  gc_basic_clause_elim:                   0
% 7.34/1.49  forced_gc_time:                         0
% 7.34/1.49  parsing_time:                           0.012
% 7.34/1.49  unif_index_cands_time:                  0.
% 7.34/1.49  unif_index_add_time:                    0.
% 7.34/1.49  orderings_time:                         0.
% 7.34/1.49  out_proof_time:                         0.02
% 7.34/1.49  total_time:                             0.596
% 7.34/1.49  num_of_symbols:                         61
% 7.34/1.49  num_of_terms:                           17875
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing
% 7.34/1.49  
% 7.34/1.49  num_of_splits:                          0
% 7.34/1.49  num_of_split_atoms:                     0
% 7.34/1.49  num_of_reused_defs:                     0
% 7.34/1.49  num_eq_ax_congr_red:                    32
% 7.34/1.49  num_of_sem_filtered_clauses:            1
% 7.34/1.49  num_of_subtypes:                        0
% 7.34/1.49  monotx_restored_types:                  0
% 7.34/1.49  sat_num_of_epr_types:                   0
% 7.34/1.49  sat_num_of_non_cyclic_types:            0
% 7.34/1.49  sat_guarded_non_collapsed_types:        0
% 7.34/1.49  num_pure_diseq_elim:                    0
% 7.34/1.49  simp_replaced_by:                       0
% 7.34/1.49  res_preprocessed:                       263
% 7.34/1.49  prep_upred:                             0
% 7.34/1.49  prep_unflattend:                        38
% 7.34/1.49  smt_new_axioms:                         0
% 7.34/1.49  pred_elim_cands:                        10
% 7.34/1.49  pred_elim:                              3
% 7.34/1.49  pred_elim_cl:                           6
% 7.34/1.49  pred_elim_cycles:                       7
% 7.34/1.49  merged_defs:                            16
% 7.34/1.49  merged_defs_ncl:                        0
% 7.34/1.49  bin_hyper_res:                          17
% 7.34/1.49  prep_cycles:                            4
% 7.34/1.49  pred_elim_time:                         0.027
% 7.34/1.49  splitting_time:                         0.
% 7.34/1.49  sem_filter_time:                        0.
% 7.34/1.49  monotx_time:                            0.
% 7.34/1.49  subtype_inf_time:                       0.
% 7.34/1.49  
% 7.34/1.49  ------ Problem properties
% 7.34/1.49  
% 7.34/1.49  clauses:                                54
% 7.34/1.49  conjectures:                            11
% 7.34/1.49  epr:                                    13
% 7.34/1.49  horn:                                   48
% 7.34/1.49  ground:                                 12
% 7.34/1.49  unary:                                  24
% 7.34/1.49  binary:                                 16
% 7.34/1.49  lits:                                   134
% 7.34/1.49  lits_eq:                                12
% 7.34/1.49  fd_pure:                                0
% 7.34/1.49  fd_pseudo:                              0
% 7.34/1.49  fd_cond:                                3
% 7.34/1.49  fd_pseudo_cond:                         2
% 7.34/1.49  ac_symbols:                             0
% 7.34/1.49  
% 7.34/1.49  ------ Propositional Solver
% 7.34/1.49  
% 7.34/1.49  prop_solver_calls:                      27
% 7.34/1.49  prop_fast_solver_calls:                 2294
% 7.34/1.49  smt_solver_calls:                       0
% 7.34/1.49  smt_fast_solver_calls:                  0
% 7.34/1.49  prop_num_of_clauses:                    7234
% 7.34/1.49  prop_preprocess_simplified:             17002
% 7.34/1.49  prop_fo_subsumed:                       112
% 7.34/1.49  prop_solver_time:                       0.
% 7.34/1.49  smt_solver_time:                        0.
% 7.34/1.49  smt_fast_solver_time:                   0.
% 7.34/1.49  prop_fast_solver_time:                  0.
% 7.34/1.49  prop_unsat_core_time:                   0.
% 7.34/1.49  
% 7.34/1.49  ------ QBF
% 7.34/1.49  
% 7.34/1.49  qbf_q_res:                              0
% 7.34/1.49  qbf_num_tautologies:                    0
% 7.34/1.49  qbf_prep_cycles:                        0
% 7.34/1.49  
% 7.34/1.49  ------ BMC1
% 7.34/1.49  
% 7.34/1.49  bmc1_current_bound:                     -1
% 7.34/1.49  bmc1_last_solved_bound:                 -1
% 7.34/1.49  bmc1_unsat_core_size:                   -1
% 7.34/1.49  bmc1_unsat_core_parents_size:           -1
% 7.34/1.49  bmc1_merge_next_fun:                    0
% 7.34/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.34/1.49  
% 7.34/1.49  ------ Instantiation
% 7.34/1.49  
% 7.34/1.49  inst_num_of_clauses:                    1813
% 7.34/1.49  inst_num_in_passive:                    515
% 7.34/1.49  inst_num_in_active:                     742
% 7.34/1.49  inst_num_in_unprocessed:                557
% 7.34/1.49  inst_num_of_loops:                      880
% 7.34/1.49  inst_num_of_learning_restarts:          0
% 7.34/1.49  inst_num_moves_active_passive:          137
% 7.34/1.49  inst_lit_activity:                      0
% 7.34/1.49  inst_lit_activity_moves:                0
% 7.34/1.49  inst_num_tautologies:                   0
% 7.34/1.49  inst_num_prop_implied:                  0
% 7.34/1.49  inst_num_existing_simplified:           0
% 7.34/1.49  inst_num_eq_res_simplified:             0
% 7.34/1.49  inst_num_child_elim:                    0
% 7.34/1.49  inst_num_of_dismatching_blockings:      593
% 7.34/1.49  inst_num_of_non_proper_insts:           1375
% 7.34/1.49  inst_num_of_duplicates:                 0
% 7.34/1.49  inst_inst_num_from_inst_to_res:         0
% 7.34/1.49  inst_dismatching_checking_time:         0.
% 7.34/1.49  
% 7.34/1.49  ------ Resolution
% 7.34/1.49  
% 7.34/1.49  res_num_of_clauses:                     0
% 7.34/1.49  res_num_in_passive:                     0
% 7.34/1.49  res_num_in_active:                      0
% 7.34/1.49  res_num_of_loops:                       267
% 7.34/1.49  res_forward_subset_subsumed:            118
% 7.34/1.49  res_backward_subset_subsumed:           6
% 7.34/1.49  res_forward_subsumed:                   0
% 7.34/1.49  res_backward_subsumed:                  0
% 7.34/1.49  res_forward_subsumption_resolution:     0
% 7.34/1.49  res_backward_subsumption_resolution:    0
% 7.34/1.49  res_clause_to_clause_subsumption:       1593
% 7.34/1.49  res_orphan_elimination:                 0
% 7.34/1.49  res_tautology_del:                      87
% 7.34/1.49  res_num_eq_res_simplified:              0
% 7.34/1.49  res_num_sel_changes:                    0
% 7.34/1.49  res_moves_from_active_to_pass:          0
% 7.34/1.49  
% 7.34/1.49  ------ Superposition
% 7.34/1.49  
% 7.34/1.49  sup_time_total:                         0.
% 7.34/1.49  sup_time_generating:                    0.
% 7.34/1.49  sup_time_sim_full:                      0.
% 7.34/1.49  sup_time_sim_immed:                     0.
% 7.34/1.49  
% 7.34/1.49  sup_num_of_clauses:                     326
% 7.34/1.49  sup_num_in_active:                      105
% 7.34/1.49  sup_num_in_passive:                     221
% 7.34/1.49  sup_num_of_loops:                       175
% 7.34/1.49  sup_fw_superposition:                   394
% 7.34/1.49  sup_bw_superposition:                   312
% 7.34/1.49  sup_immediate_simplified:               178
% 7.34/1.49  sup_given_eliminated:                   0
% 7.34/1.49  comparisons_done:                       0
% 7.34/1.49  comparisons_avoided:                    15
% 7.34/1.49  
% 7.34/1.49  ------ Simplifications
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  sim_fw_subset_subsumed:                 80
% 7.34/1.49  sim_bw_subset_subsumed:                 165
% 7.34/1.49  sim_fw_subsumed:                        37
% 7.34/1.49  sim_bw_subsumed:                        11
% 7.34/1.49  sim_fw_subsumption_res:                 12
% 7.34/1.49  sim_bw_subsumption_res:                 0
% 7.34/1.49  sim_tautology_del:                      17
% 7.34/1.49  sim_eq_tautology_del:                   10
% 7.34/1.49  sim_eq_res_simp:                        0
% 7.34/1.49  sim_fw_demodulated:                     34
% 7.34/1.49  sim_bw_demodulated:                     40
% 7.34/1.49  sim_light_normalised:                   23
% 7.34/1.49  sim_joinable_taut:                      0
% 7.34/1.49  sim_joinable_simp:                      0
% 7.34/1.49  sim_ac_normalised:                      0
% 7.34/1.49  sim_smt_subsumption:                    0
% 7.34/1.49  
%------------------------------------------------------------------------------
