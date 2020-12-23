%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:50 EST 2020

% Result     : Theorem 15.80s
% Output     : CNFRefutation 15.80s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_8877)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f75,plain,(
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
    inference(nnf_transformation,[],[f57])).

fof(f76,plain,(
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
    inference(flattening,[],[f75])).

fof(f80,plain,(
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
     => ( ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK8 = X2
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
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
              | ~ v5_pre_topc(sK7,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK7,X0,X1) )
            & sK7 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
                  | ~ v5_pre_topc(X2,X0,sK6) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
                  | v5_pre_topc(X2,X0,sK6) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK6))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK6)
        & v2_pre_topc(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK5,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK5,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,
    ( ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
      | ~ v5_pre_topc(sK7,sK5,sK6) )
    & ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
      | v5_pre_topc(sK7,sK5,sK6) )
    & sK7 = sK8
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    & v1_funct_1(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f76,f80,f79,f78,f77])).

fof(f132,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
    inference(cnf_transformation,[],[f81])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(X0)
    <=> ! [X1,X2,X3] :
          ( ( r2_hidden(k4_tarski(X1,X3),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) )
         => X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
    <=> ! [X1,X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X1,X3),X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
    <=> ! [X1,X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X1,X3),X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        | ? [X1,X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X1,X3),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) ) )
      & ( ! [X1,X2,X3] :
            ( X2 = X3
            | ~ r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) )
        | ~ v1_funct_1(X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        | ? [X1,X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X1,X3),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) ) )
      & ( ! [X4,X5,X6] :
            ( X5 = X6
            | ~ r2_hidden(k4_tarski(X4,X6),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0) )
        | ~ v1_funct_1(X0) ) ) ),
    inference(rectify,[],[f67])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK3(X0) != sK4(X0)
        & r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        | ( sK3(X0) != sK4(X0)
          & r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
          & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) )
      & ( ! [X4,X5,X6] :
            ( X5 = X6
            | ~ r2_hidden(k4_tarski(X4,X6),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0) )
        | ~ v1_funct_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f68,f69])).

fof(f95,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f131,plain,(
    v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(cnf_transformation,[],[f81])).

fof(f129,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f81])).

fof(f133,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f81])).

fof(f128,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f81])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f62,f63])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f16,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f65])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f136,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f90])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f140,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f112])).

fof(f22,axiom,(
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

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f55])).

fof(f121,plain,(
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
    inference(cnf_transformation,[],[f74])).

fof(f147,plain,(
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
    inference(equality_resolution,[],[f121])).

fof(f123,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f81])).

fof(f124,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f81])).

fof(f125,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f81])).

fof(f126,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f81])).

fof(f130,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f81])).

fof(f134,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f81])).

fof(f135,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v5_pre_topc(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f81])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f117,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f118,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f116,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f21,axiom,(
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

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f120,plain,(
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
    inference(cnf_transformation,[],[f73])).

fof(f144,plain,(
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
    inference(equality_resolution,[],[f120])).

fof(f119,plain,(
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
    inference(cnf_transformation,[],[f73])).

fof(f145,plain,(
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
    inference(equality_resolution,[],[f119])).

fof(f122,plain,(
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
    inference(cnf_transformation,[],[f74])).

fof(f146,plain,(
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
    inference(equality_resolution,[],[f122])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f137,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f89])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f141,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f111])).

fof(f96,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_5662,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_5633,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_14,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
    | v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_943,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(resolution,[status(thm)],[c_14,c_24])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_957,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_943,c_1])).

cnf(c_5621,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_957])).

cnf(c_6563,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5633,c_5621])).

cnf(c_45,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_62,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_6704,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6563,c_62])).

cnf(c_47,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_5630,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_43,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_5689,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5630,c_43])).

cnf(c_6164,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5689,c_5621])).

cnf(c_48,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_5629,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_5686,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5629,c_43])).

cnf(c_6676,plain,
    ( v1_xboole_0(u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6164,c_5686])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5659,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7403,plain,
    ( u1_struct_0(sK6) = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6676,c_5659])).

cnf(c_8206,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6704,c_7403])).

cnf(c_8337,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8206,c_5659])).

cnf(c_9435,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5662,c_8337])).

cnf(c_7404,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6704,c_5659])).

cnf(c_9969,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_9435,c_7404])).

cnf(c_10018,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_9969,c_5659])).

cnf(c_163,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4583,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_13528,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK8)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_4583])).

cnf(c_13529,plain,
    ( sK8 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13528])).

cnf(c_13531,plain,
    ( sK8 != k1_xboole_0
    | v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13529])).

cnf(c_7402,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5662,c_5659])).

cnf(c_20642,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_9969,c_7402])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5660,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5658,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_5656,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9613,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5658,c_5656])).

cnf(c_21673,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,k1_xboole_0),X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5660,c_9613])).

cnf(c_29315,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5662,c_21673])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_5664,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_5643,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_10267,plain,
    ( k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) = u1_struct_0(sK5)
    | u1_struct_0(sK6) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5689,c_5643])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_5651,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7739,plain,
    ( k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_5689,c_5651])).

cnf(c_10277,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10267,c_7739])).

cnf(c_10371,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | u1_struct_0(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10277,c_5686])).

cnf(c_10372,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(renaming,[status(thm)],[c_10371])).

cnf(c_9615,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5633,c_5656])).

cnf(c_10386,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10372,c_9615])).

cnf(c_9616,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5689,c_5656])).

cnf(c_10388,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10372,c_9616])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_10455,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10388,c_6])).

cnf(c_10890,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10386,c_163,c_10455])).

cnf(c_10891,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_10890])).

cnf(c_10898,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_5664,c_10891])).

cnf(c_10266,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),sK8) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5633,c_5643])).

cnf(c_7738,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_5633,c_5651])).

cnf(c_10284,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10266,c_7738])).

cnf(c_10296,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10284])).

cnf(c_14144,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10284,c_45,c_10296])).

cnf(c_14145,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8) ),
    inference(renaming,[status(thm)],[c_14144])).

cnf(c_5632,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_14185,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14145,c_5632])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_5647,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5811,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5647,c_6])).

cnf(c_15094,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | sK8 = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14185,c_5811])).

cnf(c_14184,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14145,c_5633])).

cnf(c_14192,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14184,c_6])).

cnf(c_15651,plain,
    ( sK8 = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15094,c_14192])).

cnf(c_15652,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_15651])).

cnf(c_15698,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | sK8 = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15652,c_5633])).

cnf(c_16608,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | sK8 = k1_xboole_0
    | v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(k1_relat_1(sK8)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15698,c_5621])).

cnf(c_21137,plain,
    ( ~ v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK8 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_21138,plain,
    ( sK8 = k1_xboole_0
    | v1_xboole_0(sK8) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21137])).

cnf(c_21296,plain,
    ( sK8 = k1_xboole_0
    | v1_xboole_0(sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16608,c_163,c_21138])).

cnf(c_21505,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10898,c_21296])).

cnf(c_40,plain,
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
    inference(cnf_transformation,[],[f147])).

cnf(c_5636,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_8439,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5633,c_5636])).

cnf(c_53,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_54,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_52,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_55,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_56,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_50,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_57,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_61,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_63,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_42,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK6)
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_5634,plain,
    ( v5_pre_topc(sK7,sK5,sK6) = iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5781,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v5_pre_topc(sK8,sK5,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5634,c_43])).

cnf(c_41,negated_conjecture,
    ( ~ v5_pre_topc(sK7,sK5,sK6)
    | ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_5635,plain,
    ( v5_pre_topc(sK7,sK5,sK6) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5792,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5635,c_43])).

cnf(c_35,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_6066,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_6067,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6066])).

cnf(c_36,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_6084,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_6085,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6084])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_6238,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_6239,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6238])).

cnf(c_37,plain,
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
    inference(cnf_transformation,[],[f144])).

cnf(c_6195,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1)
    | v5_pre_topc(X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_6620,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0)
    | v5_pre_topc(sK8,sK5,X0)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6195])).

cnf(c_7532,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | v5_pre_topc(sK8,sK5,sK6)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6620])).

cnf(c_7533,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
    | v5_pre_topc(sK8,sK5,sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7532])).

cnf(c_38,plain,
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
    inference(cnf_transformation,[],[f145])).

cnf(c_6205,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1)
    | ~ v5_pre_topc(X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_6640,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0)
    | ~ v5_pre_topc(sK8,sK5,X0)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6205])).

cnf(c_7599,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v5_pre_topc(sK8,sK5,sK6)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6640])).

cnf(c_7600,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7599])).

cnf(c_39,plain,
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
    inference(cnf_transformation,[],[f146])).

cnf(c_6287,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_6955,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0)
    | ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6287])).

cnf(c_7988,plain,
    ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6955])).

cnf(c_7989,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7988])).

cnf(c_8713,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8439,c_54,c_55,c_56,c_57,c_61,c_62,c_63,c_5781,c_5686,c_5689,c_5792,c_6067,c_6085,c_6239,c_7533,c_7600,c_7989])).

cnf(c_8714,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8713])).

cnf(c_8717,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8714,c_54,c_55,c_56,c_57,c_61,c_62,c_63,c_5781,c_5686,c_5689,c_6067,c_6085,c_6239,c_7600,c_7989])).

cnf(c_15694,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | sK8 = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15652,c_8717])).

cnf(c_23628,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | sK8 = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21505,c_15694])).

cnf(c_23669,plain,
    ( sK8 = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_21505,c_5689])).

cnf(c_23842,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | sK8 = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23628,c_23669])).

cnf(c_19172,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | sK8 = k1_xboole_0
    | v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15652,c_15694])).

cnf(c_23670,plain,
    ( sK8 = k1_xboole_0
    | v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21505,c_5686])).

cnf(c_30933,plain,
    ( sK8 = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23842,c_19172,c_23669,c_23670])).

cnf(c_30934,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_30933])).

cnf(c_31004,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_30934,c_9615])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_31037,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,sK8) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31004,c_7])).

cnf(c_34089,plain,
    ( r2_hidden(X0,sK8) != iProver_top
    | sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31037,c_163])).

cnf(c_34090,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_34089])).

cnf(c_34106,plain,
    ( sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_29315,c_34090])).

cnf(c_41853,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10018,c_163,c_13531,c_20642,c_34106])).

cnf(c_41854,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_41853])).

cnf(c_41957,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_41854,c_5632])).

cnf(c_8228,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5662,c_7404])).

cnf(c_8836,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8228,c_5659])).

cnf(c_9821,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5662,c_8836])).

cnf(c_8854,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK8)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8836])).

cnf(c_8856,plain,
    ( ~ v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8854])).

cnf(c_13530,plain,
    ( v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13528])).

cnf(c_32540,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9821,c_2,c_8856,c_13530,c_30934])).

cnf(c_32541,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_32540])).

cnf(c_5639,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_10939,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5633,c_5639])).

cnf(c_6063,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_6064,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6063])).

cnf(c_6081,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_6082,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6081])).

cnf(c_6230,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_6231,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6230])).

cnf(c_6225,plain,
    ( ~ v5_pre_topc(X0,sK5,X1)
    | v5_pre_topc(X0,sK5,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_6693,plain,
    ( ~ v5_pre_topc(sK8,sK5,X0)
    | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6225])).

cnf(c_7852,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v5_pre_topc(sK8,sK5,sK6)
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6693])).

cnf(c_7853,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v5_pre_topc(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7852])).

cnf(c_5638,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_10091,plain,
    ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5633,c_5638])).

cnf(c_6215,plain,
    ( v5_pre_topc(X0,sK5,X1)
    | ~ v5_pre_topc(X0,sK5,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_6660,plain,
    ( v5_pre_topc(sK8,sK5,X0)
    | ~ v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6215])).

cnf(c_7796,plain,
    ( ~ v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v5_pre_topc(sK8,sK5,sK6)
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6660])).

cnf(c_7797,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v5_pre_topc(sK8,sK5,sK6) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7796])).

cnf(c_10298,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10091,c_54,c_55,c_56,c_57,c_61,c_62,c_5686,c_5689,c_5792,c_6064,c_6082,c_6231,c_7797])).

cnf(c_10299,plain,
    ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10298])).

cnf(c_11275,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10939,c_54,c_55,c_56,c_57,c_61,c_62,c_5781,c_5686,c_5689,c_6064,c_6082,c_6231,c_7853,c_10299])).

cnf(c_11276,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11275])).

cnf(c_32627,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_32541,c_11276])).

cnf(c_32674,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32627,c_6])).

cnf(c_32633,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_32541,c_5633])).

cnf(c_32641,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32633,c_6])).

cnf(c_36849,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32674,c_32641])).

cnf(c_36850,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_36849])).

cnf(c_41909,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_41854,c_36850])).

cnf(c_43834,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41957,c_5686,c_41909])).

cnf(c_43835,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_43834])).

cnf(c_43900,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_43835,c_32541])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_5649,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12273,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
    | v1_partfun1(sK8,u1_struct_0(sK5)) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5689,c_5649])).

cnf(c_12715,plain,
    ( v1_partfun1(sK8,u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12273,c_61,c_5686])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_33,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_669,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_17,c_33])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_33,c_17,c_16])).

cnf(c_674,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_673])).

cnf(c_5623,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_7438,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_partfun1(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5689,c_5623])).

cnf(c_12722,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12715,c_7438])).

cnf(c_21504,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | sK8 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10898,c_5659])).

cnf(c_25467,plain,
    ( u1_struct_0(sK6) = sK8
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_12722,c_21504])).

cnf(c_37318,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(sK8,u1_pre_topc(sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_25467,c_5632])).

cnf(c_45431,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | u1_struct_0(sK5) = k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,u1_struct_0(g1_pre_topc(sK8,u1_pre_topc(sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_43900,c_37318])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_152,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_153,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4591,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_6180,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | X2 != u1_struct_0(sK6)
    | X1 != u1_struct_0(sK5)
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_4591])).

cnf(c_6182,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != u1_struct_0(sK6)
    | k1_xboole_0 != u1_struct_0(sK5)
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_6180])).

cnf(c_4582,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6448,plain,
    ( X0 != X1
    | X0 = sK8
    | sK8 != X1 ),
    inference(instantiation,[status(thm)],[c_4582])).

cnf(c_6449,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6448])).

cnf(c_9729,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != X1
    | u1_struct_0(sK6) != X2
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_4591])).

cnf(c_9731,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != k1_xboole_0
    | u1_struct_0(sK6) != k1_xboole_0
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9729])).

cnf(c_10398,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10372,c_5689])).

cnf(c_10406,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10398,c_6])).

cnf(c_10678,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10406])).

cnf(c_10389,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10372,c_8717])).

cnf(c_10448,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10389,c_6])).

cnf(c_10679,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10448])).

cnf(c_12050,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK6)
    | u1_struct_0(sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_4582])).

cnf(c_12051,plain,
    ( u1_struct_0(sK6) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12050])).

cnf(c_10396,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10372,c_5633])).

cnf(c_10807,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_10396,c_5621])).

cnf(c_4581,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6491,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_4581])).

cnf(c_7430,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_xboole_0(sK8) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7404])).

cnf(c_6175,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | X2 != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_4591])).

cnf(c_9724,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | u1_struct_0(sK6) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_6175])).

cnf(c_9725,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | u1_struct_0(sK6) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | sK8 != sK8
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9724])).

cnf(c_11133,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10448,c_10406])).

cnf(c_11134,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11133])).

cnf(c_11212,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_4581])).

cnf(c_7298,plain,
    ( X0 != X1
    | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X1 ),
    inference(instantiation,[status(thm)],[c_4582])).

cnf(c_17903,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X0
    | u1_struct_0(sK6) != X0
    | u1_struct_0(sK6) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_7298])).

cnf(c_17907,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != k1_xboole_0
    | u1_struct_0(sK6) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | u1_struct_0(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17903])).

cnf(c_19207,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10807,c_62,c_163,c_5686,c_6491,c_7430,c_9725,c_10277,c_10406,c_10448,c_10898,c_11212,c_17907])).

cnf(c_19222,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
    | u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19207,c_5659])).

cnf(c_19253,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_19222])).

cnf(c_6496,plain,
    ( X0 != X1
    | X0 = sK7
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_4582])).

cnf(c_22051,plain,
    ( X0 = sK7
    | X0 != sK8
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_6496])).

cnf(c_22052,plain,
    ( sK7 != sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 != sK8 ),
    inference(instantiation,[status(thm)],[c_22051])).

cnf(c_22467,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK5)
    | u1_struct_0(sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_4582])).

cnf(c_22468,plain,
    ( u1_struct_0(sK5) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_22467])).

cnf(c_7741,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_5651])).

cnf(c_11100,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_10406,c_7741])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_5646,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5804,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5646,c_7])).

cnf(c_22519,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | k1_relat_1(sK8) != k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11100,c_5804])).

cnf(c_22540,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | k1_relat_1(sK8) != k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22519])).

cnf(c_12274,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))) != iProver_top
    | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10396,c_5649])).

cnf(c_12272,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5633,c_5649])).

cnf(c_7302,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_17904,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_xboole_0(u1_struct_0(sK6))
    | u1_struct_0(sK6) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_7302])).

cnf(c_17905,plain,
    ( u1_struct_0(sK6) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17904])).

cnf(c_19337,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12274,c_61,c_62,c_6491,c_9725,c_10406,c_10448,c_11212,c_12272,c_12722,c_17905])).

cnf(c_7437,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5633,c_5623])).

cnf(c_19345,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_19337,c_7437])).

cnf(c_45442,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | u1_struct_0(sK5) = k1_xboole_0
    | k1_relat_1(sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_43900,c_19345])).

cnf(c_11139,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10372,c_11134])).

cnf(c_45440,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8)
    | u1_struct_0(sK5) = k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_43900,c_11139])).

cnf(c_48369,plain,
    ( u1_struct_0(sK5) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45431,c_48,c_43,c_152,c_153,c_163,c_6182,c_6449,c_9731,c_10372,c_10406,c_10678,c_10679,c_12051,c_19253,c_22052,c_22468,c_22540,c_34106,c_45442,c_45440])).

cnf(c_43895,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_43835,c_36850])).

cnf(c_48379,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))) = k1_xboole_0
    | v1_funct_2(sK8,k1_relat_1(sK8),k1_relat_1(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_48369,c_43895])).

cnf(c_45447,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
    | u1_struct_0(sK5) = k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_43900,c_14185])).

cnf(c_13,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
    | v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_138,plain,
    ( r2_hidden(k4_tarski(sK2(k1_xboole_0),sK4(k1_xboole_0)),k1_xboole_0)
    | v1_funct_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_982,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ),
    inference(resolution,[status(thm)],[c_14,c_19])).

cnf(c_984,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | r2_hidden(k4_tarski(sK2(k1_xboole_0),sK3(k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_6120,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6124,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_6120])).

cnf(c_6738,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6740,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_xboole_0),sK4(k1_xboole_0)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6738])).

cnf(c_6966,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6968,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_xboole_0),sK3(k1_xboole_0)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6966])).

cnf(c_7336,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_4581])).

cnf(c_11174,plain,
    ( X0 != X1
    | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != X1 ),
    inference(instantiation,[status(thm)],[c_4582])).

cnf(c_11175,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11174])).

cnf(c_28221,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK6))
    | u1_struct_0(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_4583])).

cnf(c_28223,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28221])).

cnf(c_28297,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_28299,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
    | ~ v1_funct_1(k1_xboole_0)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(instantiation,[status(thm)],[c_28297])).

cnf(c_8204,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5662,c_7403])).

cnf(c_8366,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | u1_struct_0(sK5) = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8204,c_5659])).

cnf(c_10014,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_9969,c_8366])).

cnf(c_8364,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(sK6) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8204,c_7404])).

cnf(c_8864,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
    | u1_struct_0(sK6) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8364,c_5659])).

cnf(c_18122,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5662,c_8864])).

cnf(c_38628,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10014,c_2,c_8877,c_13530,c_34106])).

cnf(c_38629,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_38628])).

cnf(c_38728,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_38629,c_5633])).

cnf(c_41053,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK5)) != iProver_top
    | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_38728,c_5649])).

cnf(c_7427,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7403])).

cnf(c_41597,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41053,c_163,c_7427,c_13531,c_34106])).

cnf(c_41610,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | u1_struct_0(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_41597,c_7402])).

cnf(c_45462,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_43900,c_5633])).

cnf(c_45470,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_45462,c_7])).

cnf(c_46610,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(sK5) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_45470])).

cnf(c_45458,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_43900,c_8717])).

cnf(c_45486,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_45458,c_7])).

cnf(c_46611,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(sK5) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_45486])).

cnf(c_51176,plain,
    ( v1_funct_2(X0,X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | X0 != sK8
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_6175])).

cnf(c_51178,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | k1_xboole_0 != sK8 ),
    inference(instantiation,[status(thm)],[c_51176])).

cnf(c_51422,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
    inference(instantiation,[status(thm)],[c_6120])).

cnf(c_53054,plain,
    ( u1_struct_0(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_45447,c_45,c_62,c_138,c_152,c_153,c_2,c_984,c_6124,c_6449,c_6491,c_6740,c_6968,c_7336,c_9725,c_9731,c_11175,c_11212,c_17904,c_28223,c_28299,c_34106,c_41610,c_43900,c_45470,c_46610,c_45486,c_46611,c_51178,c_51422])).

cnf(c_53057,plain,
    ( k1_relat_1(sK8) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_53054,c_48369])).

cnf(c_66031,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))) = k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48379,c_53057])).

cnf(c_8835,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8228,c_7403])).

cnf(c_9823,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8835,c_8836])).

cnf(c_9846,plain,
    ( ~ v1_xboole_0(sK8)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9823])).

cnf(c_35107,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9823,c_2,c_9846,c_13530,c_34106])).

cnf(c_35108,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5) ),
    inference(renaming,[status(thm)],[c_35107])).

cnf(c_35198,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_35108,c_5632])).

cnf(c_45433,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | u1_struct_0(sK5) = k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_43900,c_35198])).

cnf(c_149,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_151,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_676,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_6176,plain,
    ( X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | X2 != sK8
    | v1_funct_2(X2,X1,X0) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6175])).

cnf(c_6178,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | k1_xboole_0 != sK8
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6176])).

cnf(c_7304,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_7302])).

cnf(c_7737,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5658,c_5651])).

cnf(c_14048,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7737,c_5804])).

cnf(c_14065,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14048])).

cnf(c_41383,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK8,X3,X4)
    | X3 != X1
    | X4 != X2
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_4591])).

cnf(c_41384,plain,
    ( X0 != X1
    | X2 != X3
    | sK8 != X4
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(sK8,X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41383])).

cnf(c_41386,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_41384])).

cnf(c_15109,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_14192,c_7741])).

cnf(c_27213,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15109,c_8717])).

cnf(c_48410,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_48369,c_27213])).

cnf(c_48494,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_48369,c_5689])).

cnf(c_48937,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
    | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_48410,c_48494])).

cnf(c_27217,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15109,c_5633])).

cnf(c_27218,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
    | v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15109,c_5632])).

cnf(c_48466,plain,
    ( v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_48369,c_11276])).

cnf(c_51308,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_48937,c_27217,c_27218,c_48466])).

cnf(c_51314,plain,
    ( k1_relat_1(sK8) != k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_51308,c_5804])).

cnf(c_51332,plain,
    ( k1_relat_1(sK8) != k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51314])).

cnf(c_54620,plain,
    ( v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_45433,c_45,c_62,c_138,c_151,c_152,c_153,c_2,c_676,c_6124,c_6178,c_6449,c_6740,c_7304,c_7336,c_11175,c_14065,c_28299,c_32641,c_34106,c_41386,c_51178,c_51332,c_51422,c_53057])).

cnf(c_66034,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_66031,c_54620])).

cnf(c_48493,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_48369,c_5632])).

cnf(c_63569,plain,
    ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_53057,c_48493])).

cnf(c_66037,plain,
    ( v1_funct_2(sK8,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_66034,c_63569])).

cnf(c_63554,plain,
    ( v1_funct_2(sK8,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_53057,c_48466])).

cnf(c_63631,plain,
    ( v1_funct_2(sK8,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_63554,c_7])).

cnf(c_63570,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK6)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_53057,c_48494])).

cnf(c_63583,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_63570,c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66037,c_63631,c_63583])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 16:14:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.80/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.80/2.48  
% 15.80/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.80/2.48  
% 15.80/2.48  ------  iProver source info
% 15.80/2.48  
% 15.80/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.80/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.80/2.48  git: non_committed_changes: false
% 15.80/2.48  git: last_make_outside_of_git: false
% 15.80/2.48  
% 15.80/2.48  ------ 
% 15.80/2.48  
% 15.80/2.48  ------ Input Options
% 15.80/2.48  
% 15.80/2.48  --out_options                           all
% 15.80/2.48  --tptp_safe_out                         true
% 15.80/2.48  --problem_path                          ""
% 15.80/2.48  --include_path                          ""
% 15.80/2.48  --clausifier                            res/vclausify_rel
% 15.80/2.48  --clausifier_options                    --mode clausify
% 15.80/2.48  --stdin                                 false
% 15.80/2.48  --stats_out                             all
% 15.80/2.48  
% 15.80/2.48  ------ General Options
% 15.80/2.48  
% 15.80/2.48  --fof                                   false
% 15.80/2.48  --time_out_real                         305.
% 15.80/2.48  --time_out_virtual                      -1.
% 15.80/2.48  --symbol_type_check                     false
% 15.80/2.48  --clausify_out                          false
% 15.80/2.48  --sig_cnt_out                           false
% 15.80/2.48  --trig_cnt_out                          false
% 15.80/2.48  --trig_cnt_out_tolerance                1.
% 15.80/2.48  --trig_cnt_out_sk_spl                   false
% 15.80/2.48  --abstr_cl_out                          false
% 15.80/2.48  
% 15.80/2.48  ------ Global Options
% 15.80/2.48  
% 15.80/2.48  --schedule                              default
% 15.80/2.48  --add_important_lit                     false
% 15.80/2.48  --prop_solver_per_cl                    1000
% 15.80/2.48  --min_unsat_core                        false
% 15.80/2.48  --soft_assumptions                      false
% 15.80/2.48  --soft_lemma_size                       3
% 15.80/2.48  --prop_impl_unit_size                   0
% 15.80/2.48  --prop_impl_unit                        []
% 15.80/2.48  --share_sel_clauses                     true
% 15.80/2.48  --reset_solvers                         false
% 15.80/2.48  --bc_imp_inh                            [conj_cone]
% 15.80/2.48  --conj_cone_tolerance                   3.
% 15.80/2.48  --extra_neg_conj                        none
% 15.80/2.48  --large_theory_mode                     true
% 15.80/2.48  --prolific_symb_bound                   200
% 15.80/2.48  --lt_threshold                          2000
% 15.80/2.48  --clause_weak_htbl                      true
% 15.80/2.48  --gc_record_bc_elim                     false
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing Options
% 15.80/2.48  
% 15.80/2.48  --preprocessing_flag                    true
% 15.80/2.48  --time_out_prep_mult                    0.1
% 15.80/2.48  --splitting_mode                        input
% 15.80/2.48  --splitting_grd                         true
% 15.80/2.48  --splitting_cvd                         false
% 15.80/2.48  --splitting_cvd_svl                     false
% 15.80/2.48  --splitting_nvd                         32
% 15.80/2.48  --sub_typing                            true
% 15.80/2.48  --prep_gs_sim                           true
% 15.80/2.48  --prep_unflatten                        true
% 15.80/2.48  --prep_res_sim                          true
% 15.80/2.48  --prep_upred                            true
% 15.80/2.48  --prep_sem_filter                       exhaustive
% 15.80/2.48  --prep_sem_filter_out                   false
% 15.80/2.48  --pred_elim                             true
% 15.80/2.48  --res_sim_input                         true
% 15.80/2.48  --eq_ax_congr_red                       true
% 15.80/2.48  --pure_diseq_elim                       true
% 15.80/2.48  --brand_transform                       false
% 15.80/2.48  --non_eq_to_eq                          false
% 15.80/2.48  --prep_def_merge                        true
% 15.80/2.48  --prep_def_merge_prop_impl              false
% 15.80/2.48  --prep_def_merge_mbd                    true
% 15.80/2.48  --prep_def_merge_tr_red                 false
% 15.80/2.48  --prep_def_merge_tr_cl                  false
% 15.80/2.48  --smt_preprocessing                     true
% 15.80/2.48  --smt_ac_axioms                         fast
% 15.80/2.48  --preprocessed_out                      false
% 15.80/2.48  --preprocessed_stats                    false
% 15.80/2.48  
% 15.80/2.48  ------ Abstraction refinement Options
% 15.80/2.48  
% 15.80/2.48  --abstr_ref                             []
% 15.80/2.48  --abstr_ref_prep                        false
% 15.80/2.48  --abstr_ref_until_sat                   false
% 15.80/2.48  --abstr_ref_sig_restrict                funpre
% 15.80/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.80/2.48  --abstr_ref_under                       []
% 15.80/2.48  
% 15.80/2.48  ------ SAT Options
% 15.80/2.48  
% 15.80/2.48  --sat_mode                              false
% 15.80/2.48  --sat_fm_restart_options                ""
% 15.80/2.48  --sat_gr_def                            false
% 15.80/2.48  --sat_epr_types                         true
% 15.80/2.48  --sat_non_cyclic_types                  false
% 15.80/2.48  --sat_finite_models                     false
% 15.80/2.48  --sat_fm_lemmas                         false
% 15.80/2.48  --sat_fm_prep                           false
% 15.80/2.48  --sat_fm_uc_incr                        true
% 15.80/2.48  --sat_out_model                         small
% 15.80/2.48  --sat_out_clauses                       false
% 15.80/2.48  
% 15.80/2.48  ------ QBF Options
% 15.80/2.48  
% 15.80/2.48  --qbf_mode                              false
% 15.80/2.48  --qbf_elim_univ                         false
% 15.80/2.48  --qbf_dom_inst                          none
% 15.80/2.48  --qbf_dom_pre_inst                      false
% 15.80/2.48  --qbf_sk_in                             false
% 15.80/2.48  --qbf_pred_elim                         true
% 15.80/2.48  --qbf_split                             512
% 15.80/2.48  
% 15.80/2.48  ------ BMC1 Options
% 15.80/2.48  
% 15.80/2.48  --bmc1_incremental                      false
% 15.80/2.48  --bmc1_axioms                           reachable_all
% 15.80/2.48  --bmc1_min_bound                        0
% 15.80/2.48  --bmc1_max_bound                        -1
% 15.80/2.48  --bmc1_max_bound_default                -1
% 15.80/2.48  --bmc1_symbol_reachability              true
% 15.80/2.48  --bmc1_property_lemmas                  false
% 15.80/2.48  --bmc1_k_induction                      false
% 15.80/2.48  --bmc1_non_equiv_states                 false
% 15.80/2.48  --bmc1_deadlock                         false
% 15.80/2.48  --bmc1_ucm                              false
% 15.80/2.48  --bmc1_add_unsat_core                   none
% 15.80/2.48  --bmc1_unsat_core_children              false
% 15.80/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.80/2.48  --bmc1_out_stat                         full
% 15.80/2.48  --bmc1_ground_init                      false
% 15.80/2.48  --bmc1_pre_inst_next_state              false
% 15.80/2.48  --bmc1_pre_inst_state                   false
% 15.80/2.48  --bmc1_pre_inst_reach_state             false
% 15.80/2.48  --bmc1_out_unsat_core                   false
% 15.80/2.48  --bmc1_aig_witness_out                  false
% 15.80/2.48  --bmc1_verbose                          false
% 15.80/2.48  --bmc1_dump_clauses_tptp                false
% 15.80/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.80/2.48  --bmc1_dump_file                        -
% 15.80/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.80/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.80/2.48  --bmc1_ucm_extend_mode                  1
% 15.80/2.48  --bmc1_ucm_init_mode                    2
% 15.80/2.48  --bmc1_ucm_cone_mode                    none
% 15.80/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.80/2.48  --bmc1_ucm_relax_model                  4
% 15.80/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.80/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.80/2.48  --bmc1_ucm_layered_model                none
% 15.80/2.48  --bmc1_ucm_max_lemma_size               10
% 15.80/2.48  
% 15.80/2.48  ------ AIG Options
% 15.80/2.48  
% 15.80/2.48  --aig_mode                              false
% 15.80/2.48  
% 15.80/2.48  ------ Instantiation Options
% 15.80/2.48  
% 15.80/2.48  --instantiation_flag                    true
% 15.80/2.48  --inst_sos_flag                         false
% 15.80/2.48  --inst_sos_phase                        true
% 15.80/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.80/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.80/2.48  --inst_lit_sel_side                     num_symb
% 15.80/2.48  --inst_solver_per_active                1400
% 15.80/2.48  --inst_solver_calls_frac                1.
% 15.80/2.48  --inst_passive_queue_type               priority_queues
% 15.80/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.80/2.48  --inst_passive_queues_freq              [25;2]
% 15.80/2.48  --inst_dismatching                      true
% 15.80/2.48  --inst_eager_unprocessed_to_passive     true
% 15.80/2.48  --inst_prop_sim_given                   true
% 15.80/2.48  --inst_prop_sim_new                     false
% 15.80/2.48  --inst_subs_new                         false
% 15.80/2.48  --inst_eq_res_simp                      false
% 15.80/2.48  --inst_subs_given                       false
% 15.80/2.48  --inst_orphan_elimination               true
% 15.80/2.48  --inst_learning_loop_flag               true
% 15.80/2.48  --inst_learning_start                   3000
% 15.80/2.48  --inst_learning_factor                  2
% 15.80/2.48  --inst_start_prop_sim_after_learn       3
% 15.80/2.48  --inst_sel_renew                        solver
% 15.80/2.48  --inst_lit_activity_flag                true
% 15.80/2.48  --inst_restr_to_given                   false
% 15.80/2.48  --inst_activity_threshold               500
% 15.80/2.48  --inst_out_proof                        true
% 15.80/2.48  
% 15.80/2.48  ------ Resolution Options
% 15.80/2.48  
% 15.80/2.48  --resolution_flag                       true
% 15.80/2.48  --res_lit_sel                           adaptive
% 15.80/2.48  --res_lit_sel_side                      none
% 15.80/2.48  --res_ordering                          kbo
% 15.80/2.48  --res_to_prop_solver                    active
% 15.80/2.48  --res_prop_simpl_new                    false
% 15.80/2.48  --res_prop_simpl_given                  true
% 15.80/2.48  --res_passive_queue_type                priority_queues
% 15.80/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.80/2.48  --res_passive_queues_freq               [15;5]
% 15.80/2.48  --res_forward_subs                      full
% 15.80/2.48  --res_backward_subs                     full
% 15.80/2.48  --res_forward_subs_resolution           true
% 15.80/2.48  --res_backward_subs_resolution          true
% 15.80/2.48  --res_orphan_elimination                true
% 15.80/2.48  --res_time_limit                        2.
% 15.80/2.48  --res_out_proof                         true
% 15.80/2.48  
% 15.80/2.48  ------ Superposition Options
% 15.80/2.48  
% 15.80/2.48  --superposition_flag                    true
% 15.80/2.48  --sup_passive_queue_type                priority_queues
% 15.80/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.80/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.80/2.48  --demod_completeness_check              fast
% 15.80/2.48  --demod_use_ground                      true
% 15.80/2.48  --sup_to_prop_solver                    passive
% 15.80/2.48  --sup_prop_simpl_new                    true
% 15.80/2.48  --sup_prop_simpl_given                  true
% 15.80/2.48  --sup_fun_splitting                     false
% 15.80/2.48  --sup_smt_interval                      50000
% 15.80/2.48  
% 15.80/2.48  ------ Superposition Simplification Setup
% 15.80/2.48  
% 15.80/2.48  --sup_indices_passive                   []
% 15.80/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.80/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_full_bw                           [BwDemod]
% 15.80/2.48  --sup_immed_triv                        [TrivRules]
% 15.80/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.80/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_immed_bw_main                     []
% 15.80/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.80/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.80/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.80/2.48  
% 15.80/2.48  ------ Combination Options
% 15.80/2.48  
% 15.80/2.48  --comb_res_mult                         3
% 15.80/2.48  --comb_sup_mult                         2
% 15.80/2.48  --comb_inst_mult                        10
% 15.80/2.48  
% 15.80/2.48  ------ Debug Options
% 15.80/2.48  
% 15.80/2.48  --dbg_backtrace                         false
% 15.80/2.48  --dbg_dump_prop_clauses                 false
% 15.80/2.48  --dbg_dump_prop_clauses_file            -
% 15.80/2.48  --dbg_out_stat                          false
% 15.80/2.48  ------ Parsing...
% 15.80/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.80/2.48  ------ Proving...
% 15.80/2.48  ------ Problem Properties 
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  clauses                                 48
% 15.80/2.48  conjectures                             13
% 15.80/2.48  EPR                                     10
% 15.80/2.48  Horn                                    36
% 15.80/2.48  unary                                   15
% 15.80/2.48  binary                                  11
% 15.80/2.48  lits                                    144
% 15.80/2.48  lits eq                                 22
% 15.80/2.48  fd_pure                                 0
% 15.80/2.48  fd_pseudo                               0
% 15.80/2.48  fd_cond                                 4
% 15.80/2.48  fd_pseudo_cond                          5
% 15.80/2.48  AC symbols                              0
% 15.80/2.48  
% 15.80/2.48  ------ Schedule dynamic 5 is on 
% 15.80/2.48  
% 15.80/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  ------ 
% 15.80/2.48  Current options:
% 15.80/2.48  ------ 
% 15.80/2.48  
% 15.80/2.48  ------ Input Options
% 15.80/2.48  
% 15.80/2.48  --out_options                           all
% 15.80/2.48  --tptp_safe_out                         true
% 15.80/2.48  --problem_path                          ""
% 15.80/2.48  --include_path                          ""
% 15.80/2.48  --clausifier                            res/vclausify_rel
% 15.80/2.48  --clausifier_options                    --mode clausify
% 15.80/2.48  --stdin                                 false
% 15.80/2.48  --stats_out                             all
% 15.80/2.48  
% 15.80/2.48  ------ General Options
% 15.80/2.48  
% 15.80/2.48  --fof                                   false
% 15.80/2.48  --time_out_real                         305.
% 15.80/2.48  --time_out_virtual                      -1.
% 15.80/2.48  --symbol_type_check                     false
% 15.80/2.48  --clausify_out                          false
% 15.80/2.48  --sig_cnt_out                           false
% 15.80/2.48  --trig_cnt_out                          false
% 15.80/2.48  --trig_cnt_out_tolerance                1.
% 15.80/2.48  --trig_cnt_out_sk_spl                   false
% 15.80/2.48  --abstr_cl_out                          false
% 15.80/2.48  
% 15.80/2.48  ------ Global Options
% 15.80/2.48  
% 15.80/2.48  --schedule                              default
% 15.80/2.48  --add_important_lit                     false
% 15.80/2.48  --prop_solver_per_cl                    1000
% 15.80/2.48  --min_unsat_core                        false
% 15.80/2.48  --soft_assumptions                      false
% 15.80/2.48  --soft_lemma_size                       3
% 15.80/2.48  --prop_impl_unit_size                   0
% 15.80/2.48  --prop_impl_unit                        []
% 15.80/2.48  --share_sel_clauses                     true
% 15.80/2.48  --reset_solvers                         false
% 15.80/2.48  --bc_imp_inh                            [conj_cone]
% 15.80/2.48  --conj_cone_tolerance                   3.
% 15.80/2.48  --extra_neg_conj                        none
% 15.80/2.48  --large_theory_mode                     true
% 15.80/2.48  --prolific_symb_bound                   200
% 15.80/2.48  --lt_threshold                          2000
% 15.80/2.48  --clause_weak_htbl                      true
% 15.80/2.48  --gc_record_bc_elim                     false
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing Options
% 15.80/2.48  
% 15.80/2.48  --preprocessing_flag                    true
% 15.80/2.48  --time_out_prep_mult                    0.1
% 15.80/2.48  --splitting_mode                        input
% 15.80/2.48  --splitting_grd                         true
% 15.80/2.48  --splitting_cvd                         false
% 15.80/2.48  --splitting_cvd_svl                     false
% 15.80/2.48  --splitting_nvd                         32
% 15.80/2.48  --sub_typing                            true
% 15.80/2.48  --prep_gs_sim                           true
% 15.80/2.48  --prep_unflatten                        true
% 15.80/2.48  --prep_res_sim                          true
% 15.80/2.48  --prep_upred                            true
% 15.80/2.48  --prep_sem_filter                       exhaustive
% 15.80/2.48  --prep_sem_filter_out                   false
% 15.80/2.48  --pred_elim                             true
% 15.80/2.48  --res_sim_input                         true
% 15.80/2.48  --eq_ax_congr_red                       true
% 15.80/2.48  --pure_diseq_elim                       true
% 15.80/2.48  --brand_transform                       false
% 15.80/2.48  --non_eq_to_eq                          false
% 15.80/2.48  --prep_def_merge                        true
% 15.80/2.48  --prep_def_merge_prop_impl              false
% 15.80/2.48  --prep_def_merge_mbd                    true
% 15.80/2.48  --prep_def_merge_tr_red                 false
% 15.80/2.48  --prep_def_merge_tr_cl                  false
% 15.80/2.48  --smt_preprocessing                     true
% 15.80/2.48  --smt_ac_axioms                         fast
% 15.80/2.48  --preprocessed_out                      false
% 15.80/2.48  --preprocessed_stats                    false
% 15.80/2.48  
% 15.80/2.48  ------ Abstraction refinement Options
% 15.80/2.48  
% 15.80/2.48  --abstr_ref                             []
% 15.80/2.48  --abstr_ref_prep                        false
% 15.80/2.48  --abstr_ref_until_sat                   false
% 15.80/2.48  --abstr_ref_sig_restrict                funpre
% 15.80/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.80/2.48  --abstr_ref_under                       []
% 15.80/2.48  
% 15.80/2.48  ------ SAT Options
% 15.80/2.48  
% 15.80/2.48  --sat_mode                              false
% 15.80/2.48  --sat_fm_restart_options                ""
% 15.80/2.48  --sat_gr_def                            false
% 15.80/2.48  --sat_epr_types                         true
% 15.80/2.48  --sat_non_cyclic_types                  false
% 15.80/2.48  --sat_finite_models                     false
% 15.80/2.48  --sat_fm_lemmas                         false
% 15.80/2.48  --sat_fm_prep                           false
% 15.80/2.48  --sat_fm_uc_incr                        true
% 15.80/2.48  --sat_out_model                         small
% 15.80/2.48  --sat_out_clauses                       false
% 15.80/2.48  
% 15.80/2.48  ------ QBF Options
% 15.80/2.48  
% 15.80/2.48  --qbf_mode                              false
% 15.80/2.48  --qbf_elim_univ                         false
% 15.80/2.48  --qbf_dom_inst                          none
% 15.80/2.48  --qbf_dom_pre_inst                      false
% 15.80/2.48  --qbf_sk_in                             false
% 15.80/2.48  --qbf_pred_elim                         true
% 15.80/2.48  --qbf_split                             512
% 15.80/2.48  
% 15.80/2.48  ------ BMC1 Options
% 15.80/2.48  
% 15.80/2.48  --bmc1_incremental                      false
% 15.80/2.48  --bmc1_axioms                           reachable_all
% 15.80/2.48  --bmc1_min_bound                        0
% 15.80/2.48  --bmc1_max_bound                        -1
% 15.80/2.48  --bmc1_max_bound_default                -1
% 15.80/2.48  --bmc1_symbol_reachability              true
% 15.80/2.48  --bmc1_property_lemmas                  false
% 15.80/2.48  --bmc1_k_induction                      false
% 15.80/2.48  --bmc1_non_equiv_states                 false
% 15.80/2.48  --bmc1_deadlock                         false
% 15.80/2.48  --bmc1_ucm                              false
% 15.80/2.48  --bmc1_add_unsat_core                   none
% 15.80/2.48  --bmc1_unsat_core_children              false
% 15.80/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.80/2.48  --bmc1_out_stat                         full
% 15.80/2.48  --bmc1_ground_init                      false
% 15.80/2.48  --bmc1_pre_inst_next_state              false
% 15.80/2.48  --bmc1_pre_inst_state                   false
% 15.80/2.48  --bmc1_pre_inst_reach_state             false
% 15.80/2.48  --bmc1_out_unsat_core                   false
% 15.80/2.48  --bmc1_aig_witness_out                  false
% 15.80/2.48  --bmc1_verbose                          false
% 15.80/2.48  --bmc1_dump_clauses_tptp                false
% 15.80/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.80/2.48  --bmc1_dump_file                        -
% 15.80/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.80/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.80/2.48  --bmc1_ucm_extend_mode                  1
% 15.80/2.48  --bmc1_ucm_init_mode                    2
% 15.80/2.48  --bmc1_ucm_cone_mode                    none
% 15.80/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.80/2.48  --bmc1_ucm_relax_model                  4
% 15.80/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.80/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.80/2.48  --bmc1_ucm_layered_model                none
% 15.80/2.48  --bmc1_ucm_max_lemma_size               10
% 15.80/2.48  
% 15.80/2.48  ------ AIG Options
% 15.80/2.48  
% 15.80/2.48  --aig_mode                              false
% 15.80/2.48  
% 15.80/2.48  ------ Instantiation Options
% 15.80/2.48  
% 15.80/2.48  --instantiation_flag                    true
% 15.80/2.48  --inst_sos_flag                         false
% 15.80/2.48  --inst_sos_phase                        true
% 15.80/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.80/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.80/2.48  --inst_lit_sel_side                     none
% 15.80/2.48  --inst_solver_per_active                1400
% 15.80/2.48  --inst_solver_calls_frac                1.
% 15.80/2.48  --inst_passive_queue_type               priority_queues
% 15.80/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.80/2.48  --inst_passive_queues_freq              [25;2]
% 15.80/2.48  --inst_dismatching                      true
% 15.80/2.48  --inst_eager_unprocessed_to_passive     true
% 15.80/2.48  --inst_prop_sim_given                   true
% 15.80/2.48  --inst_prop_sim_new                     false
% 15.80/2.48  --inst_subs_new                         false
% 15.80/2.48  --inst_eq_res_simp                      false
% 15.80/2.48  --inst_subs_given                       false
% 15.80/2.48  --inst_orphan_elimination               true
% 15.80/2.48  --inst_learning_loop_flag               true
% 15.80/2.48  --inst_learning_start                   3000
% 15.80/2.48  --inst_learning_factor                  2
% 15.80/2.48  --inst_start_prop_sim_after_learn       3
% 15.80/2.48  --inst_sel_renew                        solver
% 15.80/2.48  --inst_lit_activity_flag                true
% 15.80/2.48  --inst_restr_to_given                   false
% 15.80/2.48  --inst_activity_threshold               500
% 15.80/2.48  --inst_out_proof                        true
% 15.80/2.48  
% 15.80/2.48  ------ Resolution Options
% 15.80/2.48  
% 15.80/2.48  --resolution_flag                       false
% 15.80/2.48  --res_lit_sel                           adaptive
% 15.80/2.48  --res_lit_sel_side                      none
% 15.80/2.48  --res_ordering                          kbo
% 15.80/2.48  --res_to_prop_solver                    active
% 15.80/2.48  --res_prop_simpl_new                    false
% 15.80/2.48  --res_prop_simpl_given                  true
% 15.80/2.48  --res_passive_queue_type                priority_queues
% 15.80/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.80/2.48  --res_passive_queues_freq               [15;5]
% 15.80/2.48  --res_forward_subs                      full
% 15.80/2.48  --res_backward_subs                     full
% 15.80/2.48  --res_forward_subs_resolution           true
% 15.80/2.48  --res_backward_subs_resolution          true
% 15.80/2.48  --res_orphan_elimination                true
% 15.80/2.48  --res_time_limit                        2.
% 15.80/2.48  --res_out_proof                         true
% 15.80/2.48  
% 15.80/2.48  ------ Superposition Options
% 15.80/2.48  
% 15.80/2.48  --superposition_flag                    true
% 15.80/2.48  --sup_passive_queue_type                priority_queues
% 15.80/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.80/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.80/2.48  --demod_completeness_check              fast
% 15.80/2.48  --demod_use_ground                      true
% 15.80/2.48  --sup_to_prop_solver                    passive
% 15.80/2.48  --sup_prop_simpl_new                    true
% 15.80/2.48  --sup_prop_simpl_given                  true
% 15.80/2.48  --sup_fun_splitting                     false
% 15.80/2.48  --sup_smt_interval                      50000
% 15.80/2.48  
% 15.80/2.48  ------ Superposition Simplification Setup
% 15.80/2.48  
% 15.80/2.48  --sup_indices_passive                   []
% 15.80/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.80/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_full_bw                           [BwDemod]
% 15.80/2.48  --sup_immed_triv                        [TrivRules]
% 15.80/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.80/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_immed_bw_main                     []
% 15.80/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.80/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.80/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.80/2.48  
% 15.80/2.48  ------ Combination Options
% 15.80/2.48  
% 15.80/2.48  --comb_res_mult                         3
% 15.80/2.48  --comb_sup_mult                         2
% 15.80/2.48  --comb_inst_mult                        10
% 15.80/2.48  
% 15.80/2.48  ------ Debug Options
% 15.80/2.48  
% 15.80/2.48  --dbg_backtrace                         false
% 15.80/2.48  --dbg_dump_prop_clauses                 false
% 15.80/2.48  --dbg_dump_prop_clauses_file            -
% 15.80/2.48  --dbg_out_stat                          false
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  ------ Proving...
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  % SZS status Theorem for theBenchmark.p
% 15.80/2.48  
% 15.80/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.80/2.48  
% 15.80/2.48  fof(f2,axiom,(
% 15.80/2.48    v1_xboole_0(k1_xboole_0)),
% 15.80/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f84,plain,(
% 15.80/2.48    v1_xboole_0(k1_xboole_0)),
% 15.80/2.48    inference(cnf_transformation,[],[f2])).
% 15.80/2.48  
% 15.80/2.48  fof(f23,conjecture,(
% 15.80/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.80/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f24,negated_conjecture,(
% 15.80/2.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.80/2.48    inference(negated_conjecture,[],[f23])).
% 15.80/2.48  
% 15.80/2.48  fof(f56,plain,(
% 15.80/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.80/2.48    inference(ennf_transformation,[],[f24])).
% 15.80/2.48  
% 15.80/2.48  fof(f57,plain,(
% 15.80/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.80/2.48    inference(flattening,[],[f56])).
% 15.80/2.48  
% 15.80/2.48  fof(f75,plain,(
% 15.80/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.80/2.48    inference(nnf_transformation,[],[f57])).
% 15.80/2.48  
% 15.80/2.48  fof(f76,plain,(
% 15.80/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.80/2.48    inference(flattening,[],[f75])).
% 15.80/2.48  
% 15.80/2.48  fof(f80,plain,(
% 15.80/2.48    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK8 = X2 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK8))) )),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f79,plain,(
% 15.80/2.48    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK7,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK7,X0,X1)) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f78,plain,(
% 15.80/2.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(X2,X0,sK6)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(X2,X0,sK6)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK6)) & v1_funct_1(X2)) & l1_pre_topc(sK6) & v2_pre_topc(sK6))) )),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f77,plain,(
% 15.80/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK5,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK5,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f81,plain,(
% 15.80/2.48    ((((~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(sK7,sK5,sK6)) & (v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6)) & sK7 = sK8 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) & v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) & v1_funct_1(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)),
% 15.80/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f76,f80,f79,f78,f77])).
% 15.80/2.48  
% 15.80/2.48  fof(f132,plain,(
% 15.80/2.48    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))),
% 15.80/2.48    inference(cnf_transformation,[],[f81])).
% 15.80/2.48  
% 15.80/2.48  fof(f9,axiom,(
% 15.80/2.48    ! [X0] : (v1_funct_1(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X2 = X3))),
% 15.80/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f33,plain,(
% 15.80/2.48    ! [X0] : (v1_funct_1(X0) <=> ! [X1,X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))))),
% 15.80/2.48    inference(ennf_transformation,[],[f9])).
% 15.80/2.48  
% 15.80/2.48  fof(f34,plain,(
% 15.80/2.48    ! [X0] : (v1_funct_1(X0) <=> ! [X1,X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))),
% 15.80/2.48    inference(flattening,[],[f33])).
% 15.80/2.48  
% 15.80/2.48  fof(f67,plain,(
% 15.80/2.48    ! [X0] : ((v1_funct_1(X0) | ? [X1,X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_funct_1(X0)))),
% 15.80/2.48    inference(nnf_transformation,[],[f34])).
% 15.80/2.48  
% 15.80/2.48  fof(f68,plain,(
% 15.80/2.48    ! [X0] : ((v1_funct_1(X0) | ? [X1,X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (X5 = X6 | ~r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v1_funct_1(X0)))),
% 15.80/2.48    inference(rectify,[],[f67])).
% 15.80/2.48  
% 15.80/2.48  fof(f69,plain,(
% 15.80/2.48    ! [X0] : (? [X1,X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK3(X0) != sK4(X0) & r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)))),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f70,plain,(
% 15.80/2.48    ! [X0] : ((v1_funct_1(X0) | (sK3(X0) != sK4(X0) & r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0))) & (! [X4,X5,X6] : (X5 = X6 | ~r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v1_funct_1(X0)))),
% 15.80/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f68,f69])).
% 15.80/2.48  
% 15.80/2.48  fof(f95,plain,(
% 15.80/2.48    ( ! [X0] : (v1_funct_1(X0) | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f70])).
% 15.80/2.48  
% 15.80/2.48  fof(f15,axiom,(
% 15.80/2.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 15.80/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f42,plain,(
% 15.80/2.48    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 15.80/2.48    inference(ennf_transformation,[],[f15])).
% 15.80/2.48  
% 15.80/2.48  fof(f43,plain,(
% 15.80/2.48    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 15.80/2.48    inference(flattening,[],[f42])).
% 15.80/2.48  
% 15.80/2.48  fof(f106,plain,(
% 15.80/2.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f43])).
% 15.80/2.48  
% 15.80/2.48  fof(f1,axiom,(
% 15.80/2.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 15.80/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f58,plain,(
% 15.80/2.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 15.80/2.48    inference(nnf_transformation,[],[f1])).
% 15.80/2.48  
% 15.80/2.48  fof(f59,plain,(
% 15.80/2.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.80/2.48    inference(rectify,[],[f58])).
% 15.80/2.48  
% 15.80/2.48  fof(f60,plain,(
% 15.80/2.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f61,plain,(
% 15.80/2.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 15.80/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f59,f60])).
% 15.80/2.48  
% 15.80/2.48  fof(f82,plain,(
% 15.80/2.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f61])).
% 15.80/2.48  
% 15.80/2.48  fof(f131,plain,(
% 15.80/2.48    v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))),
% 15.80/2.48    inference(cnf_transformation,[],[f81])).
% 15.80/2.48  
% 15.80/2.48  fof(f129,plain,(
% 15.80/2.48    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))),
% 15.80/2.48    inference(cnf_transformation,[],[f81])).
% 15.80/2.48  
% 15.80/2.48  fof(f133,plain,(
% 15.80/2.48    sK7 = sK8),
% 15.80/2.48    inference(cnf_transformation,[],[f81])).
% 15.80/2.48  
% 15.80/2.48  fof(f128,plain,(
% 15.80/2.48    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))),
% 15.80/2.48    inference(cnf_transformation,[],[f81])).
% 15.80/2.48  
% 15.80/2.48  fof(f4,axiom,(
% 15.80/2.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 15.80/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f29,plain,(
% 15.80/2.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 15.80/2.48    inference(ennf_transformation,[],[f4])).
% 15.80/2.48  
% 15.80/2.48  fof(f87,plain,(
% 15.80/2.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f29])).
% 15.80/2.49  
% 15.80/2.49  fof(f3,axiom,(
% 15.80/2.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f28,plain,(
% 15.80/2.49    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 15.80/2.49    inference(ennf_transformation,[],[f3])).
% 15.80/2.49  
% 15.80/2.49  fof(f62,plain,(
% 15.80/2.49    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 15.80/2.49    inference(nnf_transformation,[],[f28])).
% 15.80/2.49  
% 15.80/2.49  fof(f63,plain,(
% 15.80/2.49    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 15.80/2.49    introduced(choice_axiom,[])).
% 15.80/2.49  
% 15.80/2.49  fof(f64,plain,(
% 15.80/2.49    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 15.80/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f62,f63])).
% 15.80/2.49  
% 15.80/2.49  fof(f85,plain,(
% 15.80/2.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f64])).
% 15.80/2.49  
% 15.80/2.49  fof(f6,axiom,(
% 15.80/2.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f91,plain,(
% 15.80/2.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.80/2.49    inference(cnf_transformation,[],[f6])).
% 15.80/2.49  
% 15.80/2.49  fof(f8,axiom,(
% 15.80/2.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f32,plain,(
% 15.80/2.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 15.80/2.49    inference(ennf_transformation,[],[f8])).
% 15.80/2.49  
% 15.80/2.49  fof(f93,plain,(
% 15.80/2.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f32])).
% 15.80/2.49  
% 15.80/2.49  fof(f83,plain,(
% 15.80/2.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f61])).
% 15.80/2.49  
% 15.80/2.49  fof(f16,axiom,(
% 15.80/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f44,plain,(
% 15.80/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.80/2.49    inference(ennf_transformation,[],[f16])).
% 15.80/2.49  
% 15.80/2.49  fof(f45,plain,(
% 15.80/2.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.80/2.49    inference(flattening,[],[f44])).
% 15.80/2.49  
% 15.80/2.49  fof(f71,plain,(
% 15.80/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.80/2.49    inference(nnf_transformation,[],[f45])).
% 15.80/2.49  
% 15.80/2.49  fof(f108,plain,(
% 15.80/2.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.80/2.49    inference(cnf_transformation,[],[f71])).
% 15.80/2.49  
% 15.80/2.49  fof(f12,axiom,(
% 15.80/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f37,plain,(
% 15.80/2.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.80/2.49    inference(ennf_transformation,[],[f12])).
% 15.80/2.49  
% 15.80/2.49  fof(f100,plain,(
% 15.80/2.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.80/2.49    inference(cnf_transformation,[],[f37])).
% 15.80/2.49  
% 15.80/2.49  fof(f5,axiom,(
% 15.80/2.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f65,plain,(
% 15.80/2.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.80/2.49    inference(nnf_transformation,[],[f5])).
% 15.80/2.49  
% 15.80/2.49  fof(f66,plain,(
% 15.80/2.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.80/2.49    inference(flattening,[],[f65])).
% 15.80/2.49  
% 15.80/2.49  fof(f90,plain,(
% 15.80/2.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.80/2.49    inference(cnf_transformation,[],[f66])).
% 15.80/2.49  
% 15.80/2.49  fof(f136,plain,(
% 15.80/2.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.80/2.49    inference(equality_resolution,[],[f90])).
% 15.80/2.49  
% 15.80/2.49  fof(f112,plain,(
% 15.80/2.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.80/2.49    inference(cnf_transformation,[],[f71])).
% 15.80/2.49  
% 15.80/2.49  fof(f140,plain,(
% 15.80/2.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 15.80/2.49    inference(equality_resolution,[],[f112])).
% 15.80/2.49  
% 15.80/2.49  fof(f22,axiom,(
% 15.80/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f54,plain,(
% 15.80/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.80/2.49    inference(ennf_transformation,[],[f22])).
% 15.80/2.49  
% 15.80/2.49  fof(f55,plain,(
% 15.80/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.80/2.49    inference(flattening,[],[f54])).
% 15.80/2.49  
% 15.80/2.49  fof(f74,plain,(
% 15.80/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.80/2.49    inference(nnf_transformation,[],[f55])).
% 15.80/2.49  
% 15.80/2.49  fof(f121,plain,(
% 15.80/2.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f74])).
% 15.80/2.49  
% 15.80/2.49  fof(f147,plain,(
% 15.80/2.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.80/2.49    inference(equality_resolution,[],[f121])).
% 15.80/2.49  
% 15.80/2.49  fof(f123,plain,(
% 15.80/2.49    v2_pre_topc(sK5)),
% 15.80/2.49    inference(cnf_transformation,[],[f81])).
% 15.80/2.49  
% 15.80/2.49  fof(f124,plain,(
% 15.80/2.49    l1_pre_topc(sK5)),
% 15.80/2.49    inference(cnf_transformation,[],[f81])).
% 15.80/2.49  
% 15.80/2.49  fof(f125,plain,(
% 15.80/2.49    v2_pre_topc(sK6)),
% 15.80/2.49    inference(cnf_transformation,[],[f81])).
% 15.80/2.49  
% 15.80/2.49  fof(f126,plain,(
% 15.80/2.49    l1_pre_topc(sK6)),
% 15.80/2.49    inference(cnf_transformation,[],[f81])).
% 15.80/2.49  
% 15.80/2.49  fof(f130,plain,(
% 15.80/2.49    v1_funct_1(sK8)),
% 15.80/2.49    inference(cnf_transformation,[],[f81])).
% 15.80/2.49  
% 15.80/2.49  fof(f134,plain,(
% 15.80/2.49    v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | v5_pre_topc(sK7,sK5,sK6)),
% 15.80/2.49    inference(cnf_transformation,[],[f81])).
% 15.80/2.49  
% 15.80/2.49  fof(f135,plain,(
% 15.80/2.49    ~v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) | ~v5_pre_topc(sK7,sK5,sK6)),
% 15.80/2.49    inference(cnf_transformation,[],[f81])).
% 15.80/2.49  
% 15.80/2.49  fof(f19,axiom,(
% 15.80/2.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f49,plain,(
% 15.80/2.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.80/2.49    inference(ennf_transformation,[],[f19])).
% 15.80/2.49  
% 15.80/2.49  fof(f117,plain,(
% 15.80/2.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f49])).
% 15.80/2.49  
% 15.80/2.49  fof(f20,axiom,(
% 15.80/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f25,plain,(
% 15.80/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 15.80/2.49    inference(pure_predicate_removal,[],[f20])).
% 15.80/2.49  
% 15.80/2.49  fof(f50,plain,(
% 15.80/2.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.80/2.49    inference(ennf_transformation,[],[f25])).
% 15.80/2.49  
% 15.80/2.49  fof(f51,plain,(
% 15.80/2.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.80/2.49    inference(flattening,[],[f50])).
% 15.80/2.49  
% 15.80/2.49  fof(f118,plain,(
% 15.80/2.49    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f51])).
% 15.80/2.49  
% 15.80/2.49  fof(f18,axiom,(
% 15.80/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f26,plain,(
% 15.80/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 15.80/2.49    inference(pure_predicate_removal,[],[f18])).
% 15.80/2.49  
% 15.80/2.49  fof(f48,plain,(
% 15.80/2.49    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.80/2.49    inference(ennf_transformation,[],[f26])).
% 15.80/2.49  
% 15.80/2.49  fof(f116,plain,(
% 15.80/2.49    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.80/2.49    inference(cnf_transformation,[],[f48])).
% 15.80/2.49  
% 15.80/2.49  fof(f21,axiom,(
% 15.80/2.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f52,plain,(
% 15.80/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.80/2.49    inference(ennf_transformation,[],[f21])).
% 15.80/2.49  
% 15.80/2.49  fof(f53,plain,(
% 15.80/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.80/2.49    inference(flattening,[],[f52])).
% 15.80/2.49  
% 15.80/2.49  fof(f73,plain,(
% 15.80/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.80/2.49    inference(nnf_transformation,[],[f53])).
% 15.80/2.49  
% 15.80/2.49  fof(f120,plain,(
% 15.80/2.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f73])).
% 15.80/2.49  
% 15.80/2.49  fof(f144,plain,(
% 15.80/2.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.80/2.49    inference(equality_resolution,[],[f120])).
% 15.80/2.49  
% 15.80/2.49  fof(f119,plain,(
% 15.80/2.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f73])).
% 15.80/2.49  
% 15.80/2.49  fof(f145,plain,(
% 15.80/2.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.80/2.49    inference(equality_resolution,[],[f119])).
% 15.80/2.49  
% 15.80/2.49  fof(f122,plain,(
% 15.80/2.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f74])).
% 15.80/2.49  
% 15.80/2.49  fof(f146,plain,(
% 15.80/2.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.80/2.49    inference(equality_resolution,[],[f122])).
% 15.80/2.49  
% 15.80/2.49  fof(f89,plain,(
% 15.80/2.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 15.80/2.49    inference(cnf_transformation,[],[f66])).
% 15.80/2.49  
% 15.80/2.49  fof(f137,plain,(
% 15.80/2.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 15.80/2.49    inference(equality_resolution,[],[f89])).
% 15.80/2.49  
% 15.80/2.49  fof(f14,axiom,(
% 15.80/2.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f40,plain,(
% 15.80/2.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 15.80/2.49    inference(ennf_transformation,[],[f14])).
% 15.80/2.49  
% 15.80/2.49  fof(f41,plain,(
% 15.80/2.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 15.80/2.49    inference(flattening,[],[f40])).
% 15.80/2.49  
% 15.80/2.49  fof(f104,plain,(
% 15.80/2.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f41])).
% 15.80/2.49  
% 15.80/2.49  fof(f11,axiom,(
% 15.80/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f27,plain,(
% 15.80/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 15.80/2.49    inference(pure_predicate_removal,[],[f11])).
% 15.80/2.49  
% 15.80/2.49  fof(f36,plain,(
% 15.80/2.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.80/2.49    inference(ennf_transformation,[],[f27])).
% 15.80/2.49  
% 15.80/2.49  fof(f99,plain,(
% 15.80/2.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.80/2.49    inference(cnf_transformation,[],[f36])).
% 15.80/2.49  
% 15.80/2.49  fof(f17,axiom,(
% 15.80/2.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f46,plain,(
% 15.80/2.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 15.80/2.49    inference(ennf_transformation,[],[f17])).
% 15.80/2.49  
% 15.80/2.49  fof(f47,plain,(
% 15.80/2.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.80/2.49    inference(flattening,[],[f46])).
% 15.80/2.49  
% 15.80/2.49  fof(f72,plain,(
% 15.80/2.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.80/2.49    inference(nnf_transformation,[],[f47])).
% 15.80/2.49  
% 15.80/2.49  fof(f114,plain,(
% 15.80/2.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f72])).
% 15.80/2.49  
% 15.80/2.49  fof(f10,axiom,(
% 15.80/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f35,plain,(
% 15.80/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.80/2.49    inference(ennf_transformation,[],[f10])).
% 15.80/2.49  
% 15.80/2.49  fof(f98,plain,(
% 15.80/2.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.80/2.49    inference(cnf_transformation,[],[f35])).
% 15.80/2.49  
% 15.80/2.49  fof(f88,plain,(
% 15.80/2.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f66])).
% 15.80/2.49  
% 15.80/2.49  fof(f111,plain,(
% 15.80/2.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.80/2.49    inference(cnf_transformation,[],[f71])).
% 15.80/2.49  
% 15.80/2.49  fof(f141,plain,(
% 15.80/2.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 15.80/2.49    inference(equality_resolution,[],[f111])).
% 15.80/2.49  
% 15.80/2.49  fof(f96,plain,(
% 15.80/2.49    ( ! [X0] : (v1_funct_1(X0) | r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)) )),
% 15.80/2.49    inference(cnf_transformation,[],[f70])).
% 15.80/2.49  
% 15.80/2.49  fof(f13,axiom,(
% 15.80/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 15.80/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.80/2.49  
% 15.80/2.49  fof(f38,plain,(
% 15.80/2.49    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.80/2.49    inference(ennf_transformation,[],[f13])).
% 15.80/2.49  
% 15.80/2.49  fof(f39,plain,(
% 15.80/2.49    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.80/2.49    inference(flattening,[],[f38])).
% 15.80/2.49  
% 15.80/2.49  fof(f102,plain,(
% 15.80/2.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.80/2.49    inference(cnf_transformation,[],[f39])).
% 15.80/2.49  
% 15.80/2.49  cnf(c_2,plain,
% 15.80/2.49      ( v1_xboole_0(k1_xboole_0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5662,plain,
% 15.80/2.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_44,negated_conjecture,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
% 15.80/2.49      inference(cnf_transformation,[],[f132]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5633,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_14,plain,
% 15.80/2.49      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | v1_funct_1(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f95]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_24,plain,
% 15.80/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | ~ v1_funct_1(X0)
% 15.80/2.49      | ~ v1_xboole_0(X0)
% 15.80/2.49      | v1_xboole_0(X1)
% 15.80/2.49      | v1_xboole_0(X2) ),
% 15.80/2.49      inference(cnf_transformation,[],[f106]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_943,plain,
% 15.80/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
% 15.80/2.49      | ~ v1_xboole_0(X0)
% 15.80/2.49      | v1_xboole_0(X1)
% 15.80/2.49      | v1_xboole_0(X2) ),
% 15.80/2.49      inference(resolution,[status(thm)],[c_14,c_24]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_1,plain,
% 15.80/2.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 15.80/2.49      inference(cnf_transformation,[],[f82]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_957,plain,
% 15.80/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | ~ v1_xboole_0(X0)
% 15.80/2.49      | v1_xboole_0(X1)
% 15.80/2.49      | v1_xboole_0(X2) ),
% 15.80/2.49      inference(forward_subsumption_resolution,[status(thm)],[c_943,c_1]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5621,plain,
% 15.80/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(X1) = iProver_top
% 15.80/2.49      | v1_xboole_0(X2) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_957]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6563,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5633,c_5621]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_45,negated_conjecture,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
% 15.80/2.49      inference(cnf_transformation,[],[f131]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_62,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6704,plain,
% 15.80/2.49      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_6563,c_62]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_47,negated_conjecture,
% 15.80/2.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) ),
% 15.80/2.49      inference(cnf_transformation,[],[f129]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5630,plain,
% 15.80/2.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_43,negated_conjecture,
% 15.80/2.49      ( sK7 = sK8 ),
% 15.80/2.49      inference(cnf_transformation,[],[f133]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5689,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) = iProver_top ),
% 15.80/2.49      inference(light_normalisation,[status(thm)],[c_5630,c_43]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6164,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5689,c_5621]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_48,negated_conjecture,
% 15.80/2.49      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) ),
% 15.80/2.49      inference(cnf_transformation,[],[f128]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5629,plain,
% 15.80/2.49      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5686,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
% 15.80/2.49      inference(light_normalisation,[status(thm)],[c_5629,c_43]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6676,plain,
% 15.80/2.49      ( v1_xboole_0(u1_struct_0(sK6)) = iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_6164,c_5686]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5,plain,
% 15.80/2.49      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 15.80/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5659,plain,
% 15.80/2.49      ( X0 = X1
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(X1) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7403,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = X0
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_6676,c_5659]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8206,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_6704,c_7403]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8337,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_8206,c_5659]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9435,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5662,c_8337]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7404,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = X0
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_6704,c_5659]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9969,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_9435,c_7404]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10018,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_9969,c_5659]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_163,plain,
% 15.80/2.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_4583,plain,
% 15.80/2.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 15.80/2.49      theory(equality) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13528,plain,
% 15.80/2.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK8) | sK8 != X0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4583]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13529,plain,
% 15.80/2.49      ( sK8 != X0
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_13528]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13531,plain,
% 15.80/2.49      ( sK8 != k1_xboole_0
% 15.80/2.49      | v1_xboole_0(sK8) = iProver_top
% 15.80/2.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_13529]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7402,plain,
% 15.80/2.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5662,c_5659]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_20642,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_9969,c_7402]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_4,plain,
% 15.80/2.49      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 15.80/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5660,plain,
% 15.80/2.49      ( X0 = X1
% 15.80/2.49      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 15.80/2.49      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9,plain,
% 15.80/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.80/2.49      inference(cnf_transformation,[],[f91]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5658,plain,
% 15.80/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11,plain,
% 15.80/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.80/2.49      | ~ r2_hidden(X2,X0)
% 15.80/2.49      | ~ v1_xboole_0(X1) ),
% 15.80/2.49      inference(cnf_transformation,[],[f93]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5656,plain,
% 15.80/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.80/2.49      | r2_hidden(X2,X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(X1) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9613,plain,
% 15.80/2.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 15.80/2.49      | v1_xboole_0(X1) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5658,c_5656]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_21673,plain,
% 15.80/2.49      ( k1_xboole_0 = X0
% 15.80/2.49      | r2_hidden(sK1(X0,k1_xboole_0),X0) = iProver_top
% 15.80/2.49      | v1_xboole_0(X1) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5660,c_9613]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_29315,plain,
% 15.80/2.49      ( k1_xboole_0 = X0
% 15.80/2.49      | r2_hidden(sK1(X0,k1_xboole_0),X0) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5662,c_21673]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_0,plain,
% 15.80/2.49      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5664,plain,
% 15.80/2.49      ( r2_hidden(sK0(X0),X0) = iProver_top
% 15.80/2.49      | v1_xboole_0(X0) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_31,plain,
% 15.80/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | k1_relset_1(X1,X2,X0) = X1
% 15.80/2.49      | k1_xboole_0 = X2 ),
% 15.80/2.49      inference(cnf_transformation,[],[f108]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5643,plain,
% 15.80/2.49      ( k1_relset_1(X0,X1,X2) = X0
% 15.80/2.49      | k1_xboole_0 = X1
% 15.80/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.80/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10267,plain,
% 15.80/2.49      ( k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5689,c_5643]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_18,plain,
% 15.80/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f100]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5651,plain,
% 15.80/2.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.80/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7739,plain,
% 15.80/2.49      ( k1_relset_1(u1_struct_0(sK5),u1_struct_0(sK6),sK8) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5689,c_5651]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10277,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top ),
% 15.80/2.49      inference(light_normalisation,[status(thm)],[c_10267,c_7739]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10371,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(sK6) = k1_xboole_0 ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_10277,c_5686]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10372,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_10371]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9615,plain,
% 15.80/2.49      ( r2_hidden(X0,sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5633,c_5656]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10386,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | r2_hidden(X0,sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6))))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10372,c_9615]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9616,plain,
% 15.80/2.49      ( r2_hidden(X0,sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5689,c_5656]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10388,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | r2_hidden(X0,sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10372,c_9616]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6,plain,
% 15.80/2.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.80/2.49      inference(cnf_transformation,[],[f136]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10455,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | r2_hidden(X0,sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_10388,c_6]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10890,plain,
% 15.80/2.49      ( r2_hidden(X0,sK8) != iProver_top
% 15.80/2.49      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_10386,c_163,c_10455]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10891,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | r2_hidden(X0,sK8) != iProver_top ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_10890]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10898,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_xboole_0(sK8) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5664,c_10891]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10266,plain,
% 15.80/2.49      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),sK8) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5633,c_5643]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7738,plain,
% 15.80/2.49      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),sK8) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5633,c_5651]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10284,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
% 15.80/2.49      inference(light_normalisation,[status(thm)],[c_10266,c_7738]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10296,plain,
% 15.80/2.49      ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_10284]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_14144,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_10284,c_45,c_10296]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_14145,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_14144]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5632,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_14185,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_14145,c_5632]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_27,plain,
% 15.80/2.49      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 15.80/2.49      | k1_xboole_0 = X1
% 15.80/2.49      | k1_xboole_0 = X0 ),
% 15.80/2.49      inference(cnf_transformation,[],[f140]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5647,plain,
% 15.80/2.49      ( k1_xboole_0 = X0
% 15.80/2.49      | k1_xboole_0 = X1
% 15.80/2.49      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5811,plain,
% 15.80/2.49      ( k1_xboole_0 = X0
% 15.80/2.49      | k1_xboole_0 = X1
% 15.80/2.49      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_5647,c_6]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_15094,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | sK8 = k1_xboole_0
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_14185,c_5811]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_14184,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_14145,c_5633]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_14192,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_14184,c_6]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_15651,plain,
% 15.80/2.49      ( sK8 = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_15094,c_14192]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_15652,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | sK8 = k1_xboole_0 ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_15651]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_15698,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | sK8 = k1_xboole_0
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_15652,c_5633]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_16608,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | sK8 = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(k1_relat_1(sK8)) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_15698,c_5621]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_21137,plain,
% 15.80/2.49      ( ~ v1_xboole_0(sK8)
% 15.80/2.49      | ~ v1_xboole_0(k1_xboole_0)
% 15.80/2.49      | sK8 = k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_5]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_21138,plain,
% 15.80/2.49      ( sK8 = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_21137]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_21296,plain,
% 15.80/2.49      ( sK8 = k1_xboole_0 | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_16608,c_163,c_21138]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_21505,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8) | sK8 = k1_xboole_0 ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10898,c_21296]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_40,plain,
% 15.80/2.49      ( ~ v5_pre_topc(X0,X1,X2)
% 15.80/2.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 15.80/2.49      | ~ v2_pre_topc(X1)
% 15.80/2.49      | ~ v2_pre_topc(X2)
% 15.80/2.49      | ~ l1_pre_topc(X1)
% 15.80/2.49      | ~ l1_pre_topc(X2)
% 15.80/2.49      | ~ v1_funct_1(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f147]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5636,plain,
% 15.80/2.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 15.80/2.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 15.80/2.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.80/2.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 15.80/2.49      | v2_pre_topc(X1) != iProver_top
% 15.80/2.49      | v2_pre_topc(X2) != iProver_top
% 15.80/2.49      | l1_pre_topc(X1) != iProver_top
% 15.80/2.49      | l1_pre_topc(X2) != iProver_top
% 15.80/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8439,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.80/2.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.80/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK6) != iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5633,c_5636]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_53,negated_conjecture,
% 15.80/2.49      ( v2_pre_topc(sK5) ),
% 15.80/2.49      inference(cnf_transformation,[],[f123]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_54,plain,
% 15.80/2.49      ( v2_pre_topc(sK5) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_52,negated_conjecture,
% 15.80/2.49      ( l1_pre_topc(sK5) ),
% 15.80/2.49      inference(cnf_transformation,[],[f124]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_55,plain,
% 15.80/2.49      ( l1_pre_topc(sK5) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_51,negated_conjecture,
% 15.80/2.49      ( v2_pre_topc(sK6) ),
% 15.80/2.49      inference(cnf_transformation,[],[f125]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_56,plain,
% 15.80/2.49      ( v2_pre_topc(sK6) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_50,negated_conjecture,
% 15.80/2.49      ( l1_pre_topc(sK6) ),
% 15.80/2.49      inference(cnf_transformation,[],[f126]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_57,plain,
% 15.80/2.49      ( l1_pre_topc(sK6) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_46,negated_conjecture,
% 15.80/2.49      ( v1_funct_1(sK8) ),
% 15.80/2.49      inference(cnf_transformation,[],[f130]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_61,plain,
% 15.80/2.49      ( v1_funct_1(sK8) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_63,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_42,negated_conjecture,
% 15.80/2.49      ( v5_pre_topc(sK7,sK5,sK6)
% 15.80/2.49      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.80/2.49      inference(cnf_transformation,[],[f134]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5634,plain,
% 15.80/2.49      ( v5_pre_topc(sK7,sK5,sK6) = iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5781,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,sK5,sK6) = iProver_top ),
% 15.80/2.49      inference(light_normalisation,[status(thm)],[c_5634,c_43]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41,negated_conjecture,
% 15.80/2.49      ( ~ v5_pre_topc(sK7,sK5,sK6)
% 15.80/2.49      | ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.80/2.49      inference(cnf_transformation,[],[f135]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5635,plain,
% 15.80/2.49      ( v5_pre_topc(sK7,sK5,sK6) != iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5792,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,sK5,sK6) != iProver_top ),
% 15.80/2.49      inference(light_normalisation,[status(thm)],[c_5635,c_43]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_35,plain,
% 15.80/2.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 15.80/2.49      | ~ l1_pre_topc(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f117]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6066,plain,
% 15.80/2.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 15.80/2.49      | ~ l1_pre_topc(sK5) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_35]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6067,plain,
% 15.80/2.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
% 15.80/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_6066]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_36,plain,
% 15.80/2.49      ( ~ v2_pre_topc(X0)
% 15.80/2.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.80/2.49      | ~ l1_pre_topc(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f118]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6084,plain,
% 15.80/2.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(sK5) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_36]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6085,plain,
% 15.80/2.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 15.80/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK5) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_6084]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_34,plain,
% 15.80/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 15.80/2.49      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 15.80/2.49      inference(cnf_transformation,[],[f116]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6238,plain,
% 15.80/2.49      ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
% 15.80/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_34]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6239,plain,
% 15.80/2.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 15.80/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_6238]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_37,plain,
% 15.80/2.49      ( v5_pre_topc(X0,X1,X2)
% 15.80/2.49      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 15.80/2.49      | ~ v2_pre_topc(X1)
% 15.80/2.49      | ~ v2_pre_topc(X2)
% 15.80/2.49      | ~ l1_pre_topc(X1)
% 15.80/2.49      | ~ l1_pre_topc(X2)
% 15.80/2.49      | ~ v1_funct_1(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f144]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6195,plain,
% 15.80/2.49      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1)
% 15.80/2.49      | v5_pre_topc(X0,sK5,X1)
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 15.80/2.49      | ~ v2_pre_topc(X1)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(X1)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(X0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_37]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6620,plain,
% 15.80/2.49      ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0)
% 15.80/2.49      | v5_pre_topc(sK8,sK5,X0)
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(X0))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 15.80/2.49      | ~ v2_pre_topc(X0)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(X0)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(sK8) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6195]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7532,plain,
% 15.80/2.49      ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 15.80/2.49      | v5_pre_topc(sK8,sK5,sK6)
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 15.80/2.49      | ~ v2_pre_topc(sK6)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(sK6)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(sK8) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6620]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7533,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,sK5,sK6) = iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK6) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK5) != iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_7532]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_38,plain,
% 15.80/2.49      ( ~ v5_pre_topc(X0,X1,X2)
% 15.80/2.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 15.80/2.49      | ~ v2_pre_topc(X1)
% 15.80/2.49      | ~ v2_pre_topc(X2)
% 15.80/2.49      | ~ l1_pre_topc(X1)
% 15.80/2.49      | ~ l1_pre_topc(X2)
% 15.80/2.49      | ~ v1_funct_1(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f145]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6205,plain,
% 15.80/2.49      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1)
% 15.80/2.49      | ~ v5_pre_topc(X0,sK5,X1)
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 15.80/2.49      | ~ v2_pre_topc(X1)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(X1)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(X0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_38]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6640,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0)
% 15.80/2.49      | ~ v5_pre_topc(sK8,sK5,X0)
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(X0))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 15.80/2.49      | ~ v2_pre_topc(X0)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(X0)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(sK8) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6205]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7599,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 15.80/2.49      | ~ v5_pre_topc(sK8,sK5,sK6)
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 15.80/2.49      | ~ v2_pre_topc(sK6)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(sK6)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(sK8) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6640]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7600,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK6) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK5) != iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_7599]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_39,plain,
% 15.80/2.49      ( v5_pre_topc(X0,X1,X2)
% 15.80/2.49      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 15.80/2.49      | ~ v2_pre_topc(X1)
% 15.80/2.49      | ~ v2_pre_topc(X2)
% 15.80/2.49      | ~ l1_pre_topc(X1)
% 15.80/2.49      | ~ l1_pre_topc(X2)
% 15.80/2.49      | ~ v1_funct_1(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f146]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6287,plain,
% 15.80/2.49      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X1)
% 15.80/2.49      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X1))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 15.80/2.49      | ~ v2_pre_topc(X1)
% 15.80/2.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | ~ l1_pre_topc(X1)
% 15.80/2.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | ~ v1_funct_1(X0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_39]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6955,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0)
% 15.80/2.49      | ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(X0))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
% 15.80/2.49      | ~ v2_pre_topc(X0)
% 15.80/2.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | ~ l1_pre_topc(X0)
% 15.80/2.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | ~ v1_funct_1(sK8) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6287]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7988,plain,
% 15.80/2.49      ( ~ v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6)
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))))
% 15.80/2.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | ~ v2_pre_topc(sK6)
% 15.80/2.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | ~ l1_pre_topc(sK6)
% 15.80/2.49      | ~ v1_funct_1(sK8) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6955]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7989,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) = iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.80/2.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.80/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK6) != iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_7988]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8713,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_8439,c_54,c_55,c_56,c_57,c_61,c_62,c_63,c_5781,c_5686,
% 15.80/2.49                 c_5689,c_5792,c_6067,c_6085,c_6239,c_7533,c_7600,c_7989]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8714,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK6) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_8713]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8717,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)))) != iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_8714,c_54,c_55,c_56,c_57,c_61,c_62,c_63,c_5781,c_5686,
% 15.80/2.49                 c_5689,c_6067,c_6085,c_6239,c_7600,c_7989]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_15694,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | sK8 = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_15652,c_8717]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_23628,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | sK8 = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_21505,c_15694]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_23669,plain,
% 15.80/2.49      ( sK8 = k1_xboole_0
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_21505,c_5689]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_23842,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | sK8 = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top ),
% 15.80/2.49      inference(forward_subsumption_resolution,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_23628,c_23669]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_19172,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | sK8 = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_15652,c_15694]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_23670,plain,
% 15.80/2.49      ( sK8 = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(sK6)) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_21505,c_5686]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_30933,plain,
% 15.80/2.49      ( sK8 = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_23842,c_19172,c_23669,c_23670]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_30934,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | sK8 = k1_xboole_0 ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_30933]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_31004,plain,
% 15.80/2.49      ( sK8 = k1_xboole_0
% 15.80/2.49      | r2_hidden(X0,sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_30934,c_9615]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7,plain,
% 15.80/2.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.80/2.49      inference(cnf_transformation,[],[f137]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_31037,plain,
% 15.80/2.49      ( sK8 = k1_xboole_0
% 15.80/2.49      | r2_hidden(X0,sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_31004,c_7]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_34089,plain,
% 15.80/2.49      ( r2_hidden(X0,sK8) != iProver_top | sK8 = k1_xboole_0 ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_31037,c_163]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_34090,plain,
% 15.80/2.49      ( sK8 = k1_xboole_0 | r2_hidden(X0,sK8) != iProver_top ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_34089]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_34106,plain,
% 15.80/2.49      ( sK8 = k1_xboole_0 ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_29315,c_34090]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41853,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_10018,c_163,c_13531,c_20642,c_34106]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41854,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_41853]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41957,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_41854,c_5632]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8228,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5662,c_7404]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8836,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_8228,c_5659]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9821,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5662,c_8836]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8854,plain,
% 15.80/2.49      ( ~ v1_xboole_0(X0)
% 15.80/2.49      | ~ v1_xboole_0(sK8)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0 ),
% 15.80/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_8836]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8856,plain,
% 15.80/2.49      ( ~ v1_xboole_0(sK8)
% 15.80/2.49      | ~ v1_xboole_0(k1_xboole_0)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_8854]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13530,plain,
% 15.80/2.49      ( v1_xboole_0(sK8)
% 15.80/2.49      | ~ v1_xboole_0(k1_xboole_0)
% 15.80/2.49      | sK8 != k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_13528]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_32540,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_9821,c_2,c_8856,c_13530,c_30934]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_32541,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_32540]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5639,plain,
% 15.80/2.49      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 15.80/2.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 15.80/2.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.80/2.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 15.80/2.49      | v2_pre_topc(X1) != iProver_top
% 15.80/2.49      | v2_pre_topc(X2) != iProver_top
% 15.80/2.49      | l1_pre_topc(X1) != iProver_top
% 15.80/2.49      | l1_pre_topc(X2) != iProver_top
% 15.80/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10939,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.80/2.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.80/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK5) != iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5633,c_5639]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6063,plain,
% 15.80/2.49      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
% 15.80/2.49      | ~ l1_pre_topc(sK6) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_35]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6064,plain,
% 15.80/2.49      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
% 15.80/2.49      | l1_pre_topc(sK6) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_6063]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6081,plain,
% 15.80/2.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | ~ v2_pre_topc(sK6)
% 15.80/2.49      | ~ l1_pre_topc(sK6) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_36]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6082,plain,
% 15.80/2.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.80/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK6) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_6081]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6230,plain,
% 15.80/2.49      ( ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
% 15.80/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_34]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6231,plain,
% 15.80/2.49      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top
% 15.80/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_6230]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6225,plain,
% 15.80/2.49      ( ~ v5_pre_topc(X0,sK5,X1)
% 15.80/2.49      | v5_pre_topc(X0,sK5,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 15.80/2.49      | ~ v2_pre_topc(X1)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(X1)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(X0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_40]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6693,plain,
% 15.80/2.49      ( ~ v5_pre_topc(sK8,sK5,X0)
% 15.80/2.49      | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(X0))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
% 15.80/2.49      | ~ v2_pre_topc(X0)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(X0)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(sK8) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6225]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7852,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | ~ v5_pre_topc(sK8,sK5,sK6)
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 15.80/2.49      | ~ v2_pre_topc(sK6)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(sK6)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(sK8) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6693]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7853,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,sK5,sK6) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK6) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK5) != iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_7852]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5638,plain,
% 15.80/2.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 15.80/2.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 15.80/2.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.80/2.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 15.80/2.49      | v2_pre_topc(X1) != iProver_top
% 15.80/2.49      | v2_pre_topc(X2) != iProver_top
% 15.80/2.49      | l1_pre_topc(X1) != iProver_top
% 15.80/2.49      | l1_pre_topc(X2) != iProver_top
% 15.80/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10091,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.80/2.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.80/2.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK5) != iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5633,c_5638]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6215,plain,
% 15.80/2.49      ( v5_pre_topc(X0,sK5,X1)
% 15.80/2.49      | ~ v5_pre_topc(X0,sK5,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
% 15.80/2.49      | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 15.80/2.49      | ~ v2_pre_topc(X1)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(X1)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(X0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_39]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6660,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,sK5,X0)
% 15.80/2.49      | ~ v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(X0))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
% 15.80/2.49      | ~ v2_pre_topc(X0)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(X0)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(sK8) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6215]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7796,plain,
% 15.80/2.49      ( ~ v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | v5_pre_topc(sK8,sK5,sK6)
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6))))
% 15.80/2.49      | ~ v2_pre_topc(sK6)
% 15.80/2.49      | ~ v2_pre_topc(sK5)
% 15.80/2.49      | ~ l1_pre_topc(sK6)
% 15.80/2.49      | ~ l1_pre_topc(sK5)
% 15.80/2.49      | ~ v1_funct_1(sK8) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6660]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7797,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,sK5,sK6) = iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK6)))) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK6) != iProver_top
% 15.80/2.49      | v2_pre_topc(sK5) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK6) != iProver_top
% 15.80/2.49      | l1_pre_topc(sK5) != iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_7796]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10298,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_10091,c_54,c_55,c_56,c_57,c_61,c_62,c_5686,c_5689,
% 15.80/2.49                 c_5792,c_6064,c_6082,c_6231,c_7797]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10299,plain,
% 15.80/2.49      ( v5_pre_topc(sK8,sK5,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_10298]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11275,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_10939,c_54,c_55,c_56,c_57,c_61,c_62,c_5781,c_5686,
% 15.80/2.49                 c_5689,c_6064,c_6082,c_6231,c_7853,c_10299]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11276,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_11275]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_32627,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_32541,c_11276]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_32674,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_32627,c_6]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_32633,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_32541,c_5633]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_32641,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_32633,c_6]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_36849,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_32674,c_32641]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_36850,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_36849]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41909,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_41854,c_36850]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_43834,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5) ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_41957,c_5686,c_41909]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_43835,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0 ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_43834]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_43900,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK5) = k1_xboole_0 ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_43835,c_32541]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_21,plain,
% 15.80/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.80/2.49      | v1_partfun1(X0,X1)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | ~ v1_funct_1(X0)
% 15.80/2.49      | v1_xboole_0(X2) ),
% 15.80/2.49      inference(cnf_transformation,[],[f104]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5649,plain,
% 15.80/2.49      ( v1_funct_2(X0,X1,X2) != iProver_top
% 15.80/2.49      | v1_partfun1(X0,X1) = iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.80/2.49      | v1_funct_1(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(X2) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_12273,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | v1_partfun1(sK8,u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5689,c_5649]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_12715,plain,
% 15.80/2.49      ( v1_partfun1(sK8,u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_12273,c_61,c_5686]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_17,plain,
% 15.80/2.49      ( v4_relat_1(X0,X1)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 15.80/2.49      inference(cnf_transformation,[],[f99]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_33,plain,
% 15.80/2.49      ( ~ v1_partfun1(X0,X1)
% 15.80/2.49      | ~ v4_relat_1(X0,X1)
% 15.80/2.49      | ~ v1_relat_1(X0)
% 15.80/2.49      | k1_relat_1(X0) = X1 ),
% 15.80/2.49      inference(cnf_transformation,[],[f114]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_669,plain,
% 15.80/2.49      ( ~ v1_partfun1(X0,X1)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | ~ v1_relat_1(X0)
% 15.80/2.49      | k1_relat_1(X0) = X1 ),
% 15.80/2.49      inference(resolution,[status(thm)],[c_17,c_33]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_16,plain,
% 15.80/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | v1_relat_1(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f98]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_673,plain,
% 15.80/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | ~ v1_partfun1(X0,X1)
% 15.80/2.49      | k1_relat_1(X0) = X1 ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_669,c_33,c_17,c_16]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_674,plain,
% 15.80/2.49      ( ~ v1_partfun1(X0,X1)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | k1_relat_1(X0) = X1 ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_673]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5623,plain,
% 15.80/2.49      ( k1_relat_1(X0) = X1
% 15.80/2.49      | v1_partfun1(X0,X1) != iProver_top
% 15.80/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7438,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_partfun1(sK8,u1_struct_0(sK5)) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5689,c_5623]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_12722,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_12715,c_7438]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_21504,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | sK8 = X0
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10898,c_5659]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_25467,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = sK8 | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_12722,c_21504]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_37318,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(sK8,u1_pre_topc(sK6)))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_25467,c_5632]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_45431,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(sK5) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_xboole_0,u1_struct_0(g1_pre_topc(sK8,u1_pre_topc(sK6)))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_43900,c_37318]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8,plain,
% 15.80/2.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 15.80/2.49      | k1_xboole_0 = X1
% 15.80/2.49      | k1_xboole_0 = X0 ),
% 15.80/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_152,plain,
% 15.80/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.80/2.49      | k1_xboole_0 = k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_8]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_153,plain,
% 15.80/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_4591,plain,
% 15.80/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.80/2.49      | v1_funct_2(X3,X4,X5)
% 15.80/2.49      | X3 != X0
% 15.80/2.49      | X4 != X1
% 15.80/2.49      | X5 != X2 ),
% 15.80/2.49      theory(equality) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6180,plain,
% 15.80/2.49      ( v1_funct_2(X0,X1,X2)
% 15.80/2.49      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
% 15.80/2.49      | X2 != u1_struct_0(sK6)
% 15.80/2.49      | X1 != u1_struct_0(sK5)
% 15.80/2.49      | X0 != sK7 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4591]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6182,plain,
% 15.80/2.49      ( ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK6))
% 15.80/2.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 15.80/2.49      | k1_xboole_0 != u1_struct_0(sK6)
% 15.80/2.49      | k1_xboole_0 != u1_struct_0(sK5)
% 15.80/2.49      | k1_xboole_0 != sK7 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6180]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_4582,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6448,plain,
% 15.80/2.49      ( X0 != X1 | X0 = sK8 | sK8 != X1 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4582]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6449,plain,
% 15.80/2.49      ( sK8 != k1_xboole_0
% 15.80/2.49      | k1_xboole_0 = sK8
% 15.80/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6448]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9729,plain,
% 15.80/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != X1
% 15.80/2.49      | u1_struct_0(sK6) != X2
% 15.80/2.49      | sK8 != X0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4591]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9731,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 15.80/2.49      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK6) != k1_xboole_0
% 15.80/2.49      | sK8 != k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_9729]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10398,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k1_xboole_0))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10372,c_5689]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10406,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_10398,c_6]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10678,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
% 15.80/2.49      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_10406]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10389,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10372,c_8717]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10448,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_10389,c_6]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10679,plain,
% 15.80/2.49      ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
% 15.80/2.49      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_10448]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_12050,plain,
% 15.80/2.49      ( X0 != X1 | X0 = u1_struct_0(sK6) | u1_struct_0(sK6) != X1 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4582]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_12051,plain,
% 15.80/2.49      ( u1_struct_0(sK6) != k1_xboole_0
% 15.80/2.49      | k1_xboole_0 = u1_struct_0(sK6)
% 15.80/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_12050]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10396,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10372,c_5633]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10807,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10396,c_5621]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_4581,plain,( X0 = X0 ),theory(equality) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6491,plain,
% 15.80/2.49      ( sK8 = sK8 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4581]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7430,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_7404]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6175,plain,
% 15.80/2.49      ( v1_funct_2(X0,X1,X2)
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | X2 != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | X0 != sK8 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4591]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9724,plain,
% 15.80/2.49      ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | u1_struct_0(sK6) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | sK8 != sK8 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6175]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9725,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | u1_struct_0(sK6) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | sK8 != sK8
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_9724]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11133,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_10448,c_10406]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11134,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_11133]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11212,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4581]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7298,plain,
% 15.80/2.49      ( X0 != X1
% 15.80/2.49      | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X1 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4582]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_17903,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != X0
% 15.80/2.49      | u1_struct_0(sK6) != X0
% 15.80/2.49      | u1_struct_0(sK6) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_7298]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_17907,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK6) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | u1_struct_0(sK6) != k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_17903]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_19207,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_10807,c_62,c_163,c_5686,c_6491,c_7430,c_9725,c_10277,
% 15.80/2.49                 c_10406,c_10448,c_10898,c_11212,c_17907]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_19222,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
% 15.80/2.49      | u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_19207,c_5659]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_19253,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_19222]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6496,plain,
% 15.80/2.49      ( X0 != X1 | X0 = sK7 | sK7 != X1 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4582]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_22051,plain,
% 15.80/2.49      ( X0 = sK7 | X0 != sK8 | sK7 != sK8 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6496]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_22052,plain,
% 15.80/2.49      ( sK7 != sK8 | k1_xboole_0 = sK7 | k1_xboole_0 != sK8 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_22051]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_22467,plain,
% 15.80/2.49      ( X0 != X1 | X0 = u1_struct_0(sK5) | u1_struct_0(sK5) != X1 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4582]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_22468,plain,
% 15.80/2.49      ( u1_struct_0(sK5) != k1_xboole_0
% 15.80/2.49      | k1_xboole_0 = u1_struct_0(sK5)
% 15.80/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_22467]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7741,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 15.80/2.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_7,c_5651]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11100,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10406,c_7741]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_28,plain,
% 15.80/2.49      ( v1_funct_2(X0,k1_xboole_0,X1)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.80/2.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 15.80/2.49      inference(cnf_transformation,[],[f141]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5646,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 15.80/2.49      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 15.80/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_5804,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 15.80/2.49      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 15.80/2.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(light_normalisation,[status(thm)],[c_5646,c_7]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_22519,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | k1_relat_1(sK8) != k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_xboole_0,X0) = iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_11100,c_5804]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_22540,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | k1_relat_1(sK8) != k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_22519]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_12274,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK6)))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10396,c_5649]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_12272,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5633,c_5649]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7302,plain,
% 15.80/2.49      ( ~ v1_xboole_0(X0)
% 15.80/2.49      | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_5]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_17904,plain,
% 15.80/2.49      ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | ~ v1_xboole_0(u1_struct_0(sK6))
% 15.80/2.49      | u1_struct_0(sK6) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_7302]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_17905,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_17904]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_19337,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_12274,c_61,c_62,c_6491,c_9725,c_10406,c_10448,c_11212,
% 15.80/2.49                 c_12272,c_12722,c_17905]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7437,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.80/2.49      | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5633,c_5623]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_19345,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_19337,c_7437]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_45442,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(sK5) = k1_xboole_0
% 15.80/2.49      | k1_relat_1(sK8) = k1_xboole_0 ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_43900,c_19345]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11139,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_10372,c_11134]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_45440,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(sK5) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_43900,c_11139]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_48369,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_45431,c_48,c_43,c_152,c_153,c_163,c_6182,c_6449,
% 15.80/2.49                 c_9731,c_10372,c_10406,c_10678,c_10679,c_12051,c_19253,
% 15.80/2.49                 c_22052,c_22468,c_22540,c_34106,c_45442,c_45440]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_43895,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_43835,c_36850]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_48379,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_relat_1(sK8),k1_relat_1(sK8)) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_48369,c_43895]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_45447,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(sK5) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_43900,c_14185]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_13,plain,
% 15.80/2.49      ( r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0) | v1_funct_1(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f96]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_138,plain,
% 15.80/2.49      ( r2_hidden(k4_tarski(sK2(k1_xboole_0),sK4(k1_xboole_0)),k1_xboole_0)
% 15.80/2.49      | v1_funct_1(k1_xboole_0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_13]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_19,plain,
% 15.80/2.49      ( v1_funct_2(X0,X1,X2)
% 15.80/2.49      | ~ v1_partfun1(X0,X1)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | ~ v1_funct_1(X0) ),
% 15.80/2.49      inference(cnf_transformation,[],[f102]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_982,plain,
% 15.80/2.49      ( v1_funct_2(X0,X1,X2)
% 15.80/2.49      | ~ v1_partfun1(X0,X1)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.80/2.49      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ),
% 15.80/2.49      inference(resolution,[status(thm)],[c_14,c_19]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_984,plain,
% 15.80/2.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 15.80/2.49      | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
% 15.80/2.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 15.80/2.49      | r2_hidden(k4_tarski(sK2(k1_xboole_0),sK3(k1_xboole_0)),k1_xboole_0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_982]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6120,plain,
% 15.80/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_9]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6124,plain,
% 15.80/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6120]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6738,plain,
% 15.80/2.49      ( ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0) | ~ v1_xboole_0(X0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6740,plain,
% 15.80/2.49      ( ~ r2_hidden(k4_tarski(sK2(k1_xboole_0),sK4(k1_xboole_0)),k1_xboole_0)
% 15.80/2.49      | ~ v1_xboole_0(k1_xboole_0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6738]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6966,plain,
% 15.80/2.49      ( ~ r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | ~ v1_xboole_0(X0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6968,plain,
% 15.80/2.49      ( ~ r2_hidden(k4_tarski(sK2(k1_xboole_0),sK3(k1_xboole_0)),k1_xboole_0)
% 15.80/2.49      | ~ v1_xboole_0(k1_xboole_0) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6966]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7336,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4581]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11174,plain,
% 15.80/2.49      ( X0 != X1
% 15.80/2.49      | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != X1 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4582]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_11175,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != k1_xboole_0
% 15.80/2.49      | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_11174]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_28221,plain,
% 15.80/2.49      ( ~ v1_xboole_0(X0)
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK6))
% 15.80/2.49      | u1_struct_0(sK6) != X0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4583]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_28223,plain,
% 15.80/2.49      ( v1_xboole_0(u1_struct_0(sK6))
% 15.80/2.49      | ~ v1_xboole_0(k1_xboole_0)
% 15.80/2.49      | u1_struct_0(sK6) != k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_28221]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_28297,plain,
% 15.80/2.49      ( ~ v1_funct_2(X0,X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | v1_partfun1(X0,X1)
% 15.80/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
% 15.80/2.49      | ~ v1_funct_1(X0)
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_21]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_28299,plain,
% 15.80/2.49      ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | v1_partfun1(k1_xboole_0,k1_xboole_0)
% 15.80/2.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))))
% 15.80/2.49      | ~ v1_funct_1(k1_xboole_0)
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_28297]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8204,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5662,c_7403]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8366,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK5) = X0
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_8204,c_5659]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_10014,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_9969,c_8366]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8364,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_8204,c_7404]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8864,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
% 15.80/2.49      | u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(X0) != iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_8364,c_5659]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_18122,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5662,c_8864]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_38628,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5) ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_10014,c_2,c_8877,c_13530,c_34106]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_38629,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK6) = k1_xboole_0 ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_38628]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_38728,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK5)))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_38629,c_5633]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41053,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK5)) != iProver_top
% 15.80/2.49      | v1_partfun1(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = iProver_top
% 15.80/2.49      | v1_funct_1(sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_38728,c_5649]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7427,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top
% 15.80/2.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_7403]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41597,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = k1_xboole_0
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_41053,c_163,c_7427,c_13531,c_34106]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41610,plain,
% 15.80/2.49      ( u1_struct_0(sK6) = k1_xboole_0 | u1_struct_0(sK5) = k1_xboole_0 ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_41597,c_7402]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_45462,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_xboole_0
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_43900,c_5633]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_45470,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_xboole_0
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_45462,c_7]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_46610,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
% 15.80/2.49      | u1_struct_0(sK5) = k1_xboole_0 ),
% 15.80/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_45470]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_45458,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK6)))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_43900,c_8717]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_45486,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_45458,c_7]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_46611,plain,
% 15.80/2.49      ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6))
% 15.80/2.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0))
% 15.80/2.49      | u1_struct_0(sK5) = k1_xboole_0 ),
% 15.80/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_45486]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_51176,plain,
% 15.80/2.49      ( v1_funct_2(X0,X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | X0 != sK8
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6175]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_51178,plain,
% 15.80/2.49      ( ~ v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | k1_xboole_0 != sK8 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_51176]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_51422,plain,
% 15.80/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6120]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_53054,plain,
% 15.80/2.49      ( u1_struct_0(sK5) = k1_xboole_0 ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_45447,c_45,c_62,c_138,c_152,c_153,c_2,c_984,c_6124,
% 15.80/2.49                 c_6449,c_6491,c_6740,c_6968,c_7336,c_9725,c_9731,
% 15.80/2.49                 c_11175,c_11212,c_17904,c_28223,c_28299,c_34106,c_41610,
% 15.80/2.49                 c_43900,c_45470,c_46610,c_45486,c_46611,c_51178,c_51422]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_53057,plain,
% 15.80/2.49      ( k1_relat_1(sK8) = k1_xboole_0 ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_53054,c_48369]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_66031,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(light_normalisation,[status(thm)],[c_48379,c_53057]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_8835,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
% 15.80/2.49      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_8228,c_7403]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9823,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
% 15.80/2.49      | v1_xboole_0(sK8) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_8835,c_8836]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_9846,plain,
% 15.80/2.49      ( ~ v1_xboole_0(sK8)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5) ),
% 15.80/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_9823]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_35107,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0 ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_9823,c_2,c_9846,c_13530,c_34106]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_35108,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_xboole_0
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5) ),
% 15.80/2.49      inference(renaming,[status(thm)],[c_35107]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_35198,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_xboole_0) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_35108,c_5632]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_45433,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK6)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5)
% 15.80/2.49      | u1_struct_0(sK5) = k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_43900,c_35198]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_149,plain,
% 15.80/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_151,plain,
% 15.80/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_149]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_676,plain,
% 15.80/2.49      ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
% 15.80/2.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 15.80/2.49      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_674]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6176,plain,
% 15.80/2.49      ( X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | X2 != sK8
% 15.80/2.49      | v1_funct_2(X2,X1,X0) = iProver_top
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_6175]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_6178,plain,
% 15.80/2.49      ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 15.80/2.49      | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 15.80/2.49      | k1_xboole_0 != sK8
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_6176]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7304,plain,
% 15.80/2.49      ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))))
% 15.80/2.49      | ~ v1_xboole_0(k1_xboole_0)
% 15.80/2.49      | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_7302]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_7737,plain,
% 15.80/2.49      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_5658,c_5651]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_14048,plain,
% 15.80/2.49      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 15.80/2.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 15.80/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_7737,c_5804]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_14065,plain,
% 15.80/2.49      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 15.80/2.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 15.80/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_14048]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41383,plain,
% 15.80/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.80/2.49      | v1_funct_2(sK8,X3,X4)
% 15.80/2.49      | X3 != X1
% 15.80/2.49      | X4 != X2
% 15.80/2.49      | sK8 != X0 ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_4591]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41384,plain,
% 15.80/2.49      ( X0 != X1
% 15.80/2.49      | X2 != X3
% 15.80/2.49      | sK8 != X4
% 15.80/2.49      | v1_funct_2(X4,X1,X3) != iProver_top
% 15.80/2.49      | v1_funct_2(sK8,X0,X2) = iProver_top ),
% 15.80/2.49      inference(predicate_to_equality,[status(thm)],[c_41383]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_41386,plain,
% 15.80/2.49      ( sK8 != k1_xboole_0
% 15.80/2.49      | k1_xboole_0 != k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top
% 15.80/2.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_41384]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_15109,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
% 15.80/2.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_14192,c_7741]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_27213,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_15109,c_8717]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_48410,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_48369,c_27213]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_48494,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(sK6)))) = iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_48369,c_5689]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_48937,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))),u1_struct_0(sK6)) != iProver_top ),
% 15.80/2.49      inference(forward_subsumption_resolution,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_48410,c_48494]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_27217,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_15109,c_5633]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_27218,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8)
% 15.80/2.49      | v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_15109,c_5632]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_48466,plain,
% 15.80/2.49      ( v1_funct_2(sK8,k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK8),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_48369,c_11276]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_51308,plain,
% 15.80/2.49      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_relat_1(sK8) ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_48937,c_27217,c_27218,c_48466]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_51314,plain,
% 15.80/2.49      ( k1_relat_1(sK8) != k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_xboole_0,X0) = iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(superposition,[status(thm)],[c_51308,c_5804]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_51332,plain,
% 15.80/2.49      ( k1_relat_1(sK8) != k1_xboole_0
% 15.80/2.49      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(instantiation,[status(thm)],[c_51314]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_54620,plain,
% 15.80/2.49      ( v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.80/2.49      inference(global_propositional_subsumption,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_45433,c_45,c_62,c_138,c_151,c_152,c_153,c_2,c_676,
% 15.80/2.49                 c_6124,c_6178,c_6449,c_6740,c_7304,c_7336,c_11175,
% 15.80/2.49                 c_14065,c_28299,c_32641,c_34106,c_41386,c_51178,c_51332,
% 15.80/2.49                 c_51422,c_53057]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_66034,plain,
% 15.80/2.49      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))) = k1_xboole_0 ),
% 15.80/2.49      inference(forward_subsumption_resolution,
% 15.80/2.49                [status(thm)],
% 15.80/2.49                [c_66031,c_54620]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_48493,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_relat_1(sK8),u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_48369,c_5632]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_63569,plain,
% 15.80/2.49      ( v1_funct_2(sK8,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK5))),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_53057,c_48493]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_66037,plain,
% 15.80/2.49      ( v1_funct_2(sK8,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_66034,c_63569]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_63554,plain,
% 15.80/2.49      ( v1_funct_2(sK8,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))))) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_53057,c_48466]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_63631,plain,
% 15.80/2.49      ( v1_funct_2(sK8,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 15.80/2.49      | m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_63554,c_7]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_63570,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK6)))) = iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_53057,c_48494]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(c_63583,plain,
% 15.80/2.49      ( m1_subset_1(sK8,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.80/2.49      inference(demodulation,[status(thm)],[c_63570,c_7]) ).
% 15.80/2.49  
% 15.80/2.49  cnf(contradiction,plain,
% 15.80/2.49      ( $false ),
% 15.80/2.49      inference(minisat,[status(thm)],[c_66037,c_63631,c_63583]) ).
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.80/2.49  
% 15.80/2.49  ------                               Statistics
% 15.80/2.49  
% 15.80/2.49  ------ General
% 15.80/2.49  
% 15.80/2.49  abstr_ref_over_cycles:                  0
% 15.80/2.49  abstr_ref_under_cycles:                 0
% 15.80/2.49  gc_basic_clause_elim:                   0
% 15.80/2.49  forced_gc_time:                         0
% 15.80/2.49  parsing_time:                           0.012
% 15.80/2.49  unif_index_cands_time:                  0.
% 15.80/2.49  unif_index_add_time:                    0.
% 15.80/2.49  orderings_time:                         0.
% 15.80/2.49  out_proof_time:                         0.034
% 15.80/2.49  total_time:                             1.714
% 15.80/2.49  num_of_symbols:                         60
% 15.80/2.49  num_of_terms:                           24269
% 15.80/2.49  
% 15.80/2.49  ------ Preprocessing
% 15.80/2.49  
% 15.80/2.49  num_of_splits:                          0
% 15.80/2.49  num_of_split_atoms:                     0
% 15.80/2.49  num_of_reused_defs:                     0
% 15.80/2.49  num_eq_ax_congr_red:                    35
% 15.80/2.49  num_of_sem_filtered_clauses:            1
% 15.80/2.49  num_of_subtypes:                        0
% 15.80/2.49  monotx_restored_types:                  0
% 15.80/2.49  sat_num_of_epr_types:                   0
% 15.80/2.49  sat_num_of_non_cyclic_types:            0
% 15.80/2.49  sat_guarded_non_collapsed_types:        0
% 15.80/2.49  num_pure_diseq_elim:                    0
% 15.80/2.49  simp_replaced_by:                       0
% 15.80/2.49  res_preprocessed:                       231
% 15.80/2.49  prep_upred:                             0
% 15.80/2.49  prep_unflattend:                        63
% 15.80/2.49  smt_new_axioms:                         0
% 15.80/2.49  pred_elim_cands:                        9
% 15.80/2.49  pred_elim:                              2
% 15.80/2.49  pred_elim_cl:                           2
% 15.80/2.49  pred_elim_cycles:                       8
% 15.80/2.49  merged_defs:                            8
% 15.80/2.49  merged_defs_ncl:                        0
% 15.80/2.49  bin_hyper_res:                          8
% 15.80/2.49  prep_cycles:                            4
% 15.80/2.49  pred_elim_time:                         0.074
% 15.80/2.49  splitting_time:                         0.
% 15.80/2.49  sem_filter_time:                        0.
% 15.80/2.49  monotx_time:                            0.
% 15.80/2.49  subtype_inf_time:                       0.
% 15.80/2.49  
% 15.80/2.49  ------ Problem properties
% 15.80/2.49  
% 15.80/2.49  clauses:                                48
% 15.80/2.49  conjectures:                            13
% 15.80/2.49  epr:                                    10
% 15.80/2.49  horn:                                   36
% 15.80/2.49  ground:                                 14
% 15.80/2.49  unary:                                  15
% 15.80/2.49  binary:                                 11
% 15.80/2.49  lits:                                   144
% 15.80/2.49  lits_eq:                                22
% 15.80/2.49  fd_pure:                                0
% 15.80/2.49  fd_pseudo:                              0
% 15.80/2.49  fd_cond:                                4
% 15.80/2.49  fd_pseudo_cond:                         5
% 15.80/2.49  ac_symbols:                             0
% 15.80/2.49  
% 15.80/2.49  ------ Propositional Solver
% 15.80/2.49  
% 15.80/2.49  prop_solver_calls:                      29
% 15.80/2.49  prop_fast_solver_calls:                 6209
% 15.80/2.49  smt_solver_calls:                       0
% 15.80/2.49  smt_fast_solver_calls:                  0
% 15.80/2.49  prop_num_of_clauses:                    15772
% 15.80/2.49  prop_preprocess_simplified:             26108
% 15.80/2.49  prop_fo_subsumed:                       454
% 15.80/2.49  prop_solver_time:                       0.
% 15.80/2.49  smt_solver_time:                        0.
% 15.80/2.49  smt_fast_solver_time:                   0.
% 15.80/2.49  prop_fast_solver_time:                  0.
% 15.80/2.49  prop_unsat_core_time:                   0.001
% 15.80/2.49  
% 15.80/2.49  ------ QBF
% 15.80/2.49  
% 15.80/2.49  qbf_q_res:                              0
% 15.80/2.49  qbf_num_tautologies:                    0
% 15.80/2.49  qbf_prep_cycles:                        0
% 15.80/2.49  
% 15.80/2.49  ------ BMC1
% 15.80/2.49  
% 15.80/2.49  bmc1_current_bound:                     -1
% 15.80/2.49  bmc1_last_solved_bound:                 -1
% 15.80/2.49  bmc1_unsat_core_size:                   -1
% 15.80/2.49  bmc1_unsat_core_parents_size:           -1
% 15.80/2.49  bmc1_merge_next_fun:                    0
% 15.80/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.80/2.49  
% 15.80/2.49  ------ Instantiation
% 15.80/2.49  
% 15.80/2.49  inst_num_of_clauses:                    3792
% 15.80/2.49  inst_num_in_passive:                    759
% 15.80/2.49  inst_num_in_active:                     1478
% 15.80/2.49  inst_num_in_unprocessed:                1555
% 15.80/2.49  inst_num_of_loops:                      2150
% 15.80/2.49  inst_num_of_learning_restarts:          0
% 15.80/2.49  inst_num_moves_active_passive:          670
% 15.80/2.49  inst_lit_activity:                      0
% 15.80/2.49  inst_lit_activity_moves:                0
% 15.80/2.49  inst_num_tautologies:                   0
% 15.80/2.49  inst_num_prop_implied:                  0
% 15.80/2.49  inst_num_existing_simplified:           0
% 15.80/2.49  inst_num_eq_res_simplified:             0
% 15.80/2.49  inst_num_child_elim:                    0
% 15.80/2.49  inst_num_of_dismatching_blockings:      3431
% 15.80/2.49  inst_num_of_non_proper_insts:           4537
% 15.80/2.49  inst_num_of_duplicates:                 0
% 15.80/2.49  inst_inst_num_from_inst_to_res:         0
% 15.80/2.49  inst_dismatching_checking_time:         0.
% 15.80/2.49  
% 15.80/2.49  ------ Resolution
% 15.80/2.49  
% 15.80/2.49  res_num_of_clauses:                     0
% 15.80/2.49  res_num_in_passive:                     0
% 15.80/2.49  res_num_in_active:                      0
% 15.80/2.49  res_num_of_loops:                       235
% 15.80/2.49  res_forward_subset_subsumed:            216
% 15.80/2.49  res_backward_subset_subsumed:           0
% 15.80/2.49  res_forward_subsumed:                   3
% 15.80/2.49  res_backward_subsumed:                  1
% 15.80/2.49  res_forward_subsumption_resolution:     2
% 15.80/2.49  res_backward_subsumption_resolution:    0
% 15.80/2.49  res_clause_to_clause_subsumption:       5650
% 15.80/2.49  res_orphan_elimination:                 0
% 15.80/2.49  res_tautology_del:                      139
% 15.80/2.49  res_num_eq_res_simplified:              0
% 15.80/2.49  res_num_sel_changes:                    0
% 15.80/2.49  res_moves_from_active_to_pass:          0
% 15.80/2.49  
% 15.80/2.49  ------ Superposition
% 15.80/2.49  
% 15.80/2.49  sup_time_total:                         0.
% 15.80/2.49  sup_time_generating:                    0.
% 15.80/2.49  sup_time_sim_full:                      0.
% 15.80/2.49  sup_time_sim_immed:                     0.
% 15.80/2.49  
% 15.80/2.49  sup_num_of_clauses:                     656
% 15.80/2.49  sup_num_in_active:                      91
% 15.80/2.49  sup_num_in_passive:                     565
% 15.80/2.49  sup_num_of_loops:                       428
% 15.80/2.49  sup_fw_superposition:                   1229
% 15.80/2.49  sup_bw_superposition:                   1809
% 15.80/2.49  sup_immediate_simplified:               1271
% 15.80/2.49  sup_given_eliminated:                   0
% 15.80/2.49  comparisons_done:                       0
% 15.80/2.49  comparisons_avoided:                    185
% 15.80/2.49  
% 15.80/2.49  ------ Simplifications
% 15.80/2.49  
% 15.80/2.49  
% 15.80/2.49  sim_fw_subset_subsumed:                 867
% 15.80/2.49  sim_bw_subset_subsumed:                 682
% 15.80/2.49  sim_fw_subsumed:                        160
% 15.80/2.49  sim_bw_subsumed:                        54
% 15.80/2.49  sim_fw_subsumption_res:                 21
% 15.80/2.49  sim_bw_subsumption_res:                 0
% 15.80/2.49  sim_tautology_del:                      41
% 15.80/2.49  sim_eq_tautology_del:                   118
% 15.80/2.49  sim_eq_res_simp:                        0
% 15.80/2.49  sim_fw_demodulated:                     152
% 15.80/2.49  sim_bw_demodulated:                     188
% 15.80/2.49  sim_light_normalised:                   152
% 15.80/2.49  sim_joinable_taut:                      0
% 15.80/2.49  sim_joinable_simp:                      0
% 15.80/2.49  sim_ac_normalised:                      0
% 15.80/2.49  sim_smt_subsumption:                    0
% 15.80/2.49  
%------------------------------------------------------------------------------
