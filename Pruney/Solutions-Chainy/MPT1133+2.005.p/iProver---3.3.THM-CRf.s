%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:48 EST 2020

% Result     : Theorem 27.84s
% Output     : CNFRefutation 27.84s
% Verified   : 
% Statistics : Number of formulae       :  346 (33353 expanded)
%              Number of clauses        :  220 (5655 expanded)
%              Number of leaves         :   33 (10647 expanded)
%              Depth                    :   32
%              Number of atoms          : 1392 (410313 expanded)
%              Number of equality atoms :  539 (41653 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,conjecture,(
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

fof(f81,negated_conjecture,(
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
    inference(negated_conjecture,[],[f80])).

fof(f152,plain,(
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
    inference(ennf_transformation,[],[f81])).

fof(f153,plain,(
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
    inference(flattening,[],[f152])).

fof(f216,plain,(
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
    inference(nnf_transformation,[],[f153])).

fof(f217,plain,(
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
    inference(flattening,[],[f216])).

fof(f221,plain,(
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
     => ( ( ~ v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK28 = X2
        & m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK28) ) ) ),
    introduced(choice_axiom,[])).

fof(f220,plain,(
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
              | ~ v5_pre_topc(sK27,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK27,X0,X1) )
            & sK27 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK27,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK27) ) ) ),
    introduced(choice_axiom,[])).

fof(f219,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
                  | ~ v5_pre_topc(X2,X0,sK26) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
                  | v5_pre_topc(X2,X0,sK26) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK26))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK26))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK26)
        & v2_pre_topc(sK26) ) ) ),
    introduced(choice_axiom,[])).

fof(f218,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK25,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK25,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK25),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK25)
      & v2_pre_topc(sK25) ) ),
    introduced(choice_axiom,[])).

fof(f222,plain,
    ( ( ~ v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
      | ~ v5_pre_topc(sK27,sK25,sK26) )
    & ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
      | v5_pre_topc(sK27,sK25,sK26) )
    & sK27 = sK28
    & m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))))
    & v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
    & v1_funct_1(sK28)
    & m1_subset_1(sK27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))
    & v1_funct_2(sK27,u1_struct_0(sK25),u1_struct_0(sK26))
    & v1_funct_1(sK27)
    & l1_pre_topc(sK26)
    & v2_pre_topc(sK26)
    & l1_pre_topc(sK25)
    & v2_pre_topc(sK25) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25,sK26,sK27,sK28])],[f217,f221,f220,f219,f218])).

fof(f376,plain,(
    m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) ),
    inference(cnf_transformation,[],[f222])).

fof(f70,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f134,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f70])).

fof(f135,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f134])).

fof(f348,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f371,plain,(
    v1_funct_1(sK27) ),
    inference(cnf_transformation,[],[f222])).

fof(f377,plain,(
    sK27 = sK28 ),
    inference(cnf_transformation,[],[f222])).

fof(f410,plain,(
    v1_funct_1(sK28) ),
    inference(definition_unfolding,[],[f371,f377])).

fof(f375,plain,(
    v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) ),
    inference(cnf_transformation,[],[f222])).

fof(f65,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f132,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f132])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f133])).

fof(f332,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f205])).

fof(f52,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f112,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f310,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f58,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f120,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) = X1
        & r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f121,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) = X1
        & r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f120])).

fof(f319,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f69,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f347,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f69])).

fof(f400,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r1_tarski(k6_partfun1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f319,f347])).

fof(f55,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f116,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f315,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f46,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f303,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

fof(f399,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f303,f347])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f183,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f276,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f183])).

fof(f28,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f273,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f373,plain,(
    m1_subset_1(sK27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) ),
    inference(cnf_transformation,[],[f222])).

fof(f408,plain,(
    m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) ),
    inference(definition_unfolding,[],[f373,f377])).

fof(f372,plain,(
    v1_funct_2(sK27,u1_struct_0(sK25),u1_struct_0(sK26)) ),
    inference(cnf_transformation,[],[f222])).

fof(f409,plain,(
    v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) ),
    inference(definition_unfolding,[],[f372,f377])).

fof(f78,axiom,(
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

fof(f148,plain,(
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
    inference(ennf_transformation,[],[f78])).

fof(f149,plain,(
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
    inference(flattening,[],[f148])).

fof(f214,plain,(
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
    inference(nnf_transformation,[],[f149])).

fof(f364,plain,(
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
    inference(cnf_transformation,[],[f214])).

fof(f431,plain,(
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
    inference(equality_resolution,[],[f364])).

fof(f367,plain,(
    v2_pre_topc(sK25) ),
    inference(cnf_transformation,[],[f222])).

fof(f368,plain,(
    l1_pre_topc(sK25) ),
    inference(cnf_transformation,[],[f222])).

fof(f369,plain,(
    v2_pre_topc(sK26) ),
    inference(cnf_transformation,[],[f222])).

fof(f370,plain,(
    l1_pre_topc(sK26) ),
    inference(cnf_transformation,[],[f222])).

fof(f75,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f143,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f359,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f143])).

fof(f76,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f76])).

fof(f144,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f83])).

fof(f145,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f144])).

fof(f360,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f74,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f74])).

fof(f142,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f84])).

fof(f358,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f363,plain,(
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
    inference(cnf_transformation,[],[f214])).

fof(f432,plain,(
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
    inference(equality_resolution,[],[f363])).

fof(f379,plain,
    ( ~ v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | ~ v5_pre_topc(sK27,sK25,sK26) ),
    inference(cnf_transformation,[],[f222])).

fof(f406,plain,
    ( ~ v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | ~ v5_pre_topc(sK28,sK25,sK26) ),
    inference(definition_unfolding,[],[f379,f377])).

fof(f79,axiom,(
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

fof(f150,plain,(
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
    inference(ennf_transformation,[],[f79])).

fof(f151,plain,(
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
    inference(flattening,[],[f150])).

fof(f215,plain,(
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
    inference(nnf_transformation,[],[f151])).

fof(f366,plain,(
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
    inference(cnf_transformation,[],[f215])).

fof(f433,plain,(
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
    inference(equality_resolution,[],[f366])).

fof(f378,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | v5_pre_topc(sK27,sK25,sK26) ),
    inference(cnf_transformation,[],[f222])).

fof(f407,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | v5_pre_topc(sK28,sK25,sK26) ),
    inference(definition_unfolding,[],[f378,f377])).

fof(f365,plain,(
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
    inference(cnf_transformation,[],[f215])).

fof(f434,plain,(
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
    inference(equality_resolution,[],[f365])).

fof(f57,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f118,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f119,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f118])).

fof(f317,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f60,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f123,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f124,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f123])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f93])).

fof(f271,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f182])).

fof(f21,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f264,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f394,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f271,f264])).

fof(f272,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f182])).

fof(f393,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f272,f264])).

fof(f423,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f393])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f175,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f175])).

fof(f258,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f176])).

fof(f421,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f258])).

fof(f66,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f335,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f66])).

fof(f44,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f301,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

fof(f396,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f301,f347])).

fof(f61,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f125,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f71,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f136,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f137,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f136])).

fof(f352,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f137])).

fof(f333,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f205])).

fof(f429,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f333])).

cnf(c_135,negated_conjecture,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) ),
    inference(cnf_transformation,[],[f376])).

cnf(c_6005,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_135])).

cnf(c_115,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f348])).

cnf(c_6024,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_partfun1(X1,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_31075,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) = iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_6005,c_6024])).

cnf(c_140,negated_conjecture,
    ( v1_funct_1(sK28) ),
    inference(cnf_transformation,[],[f410])).

cnf(c_149,plain,
    ( v1_funct_1(sK28) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_136,negated_conjecture,
    ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) ),
    inference(cnf_transformation,[],[f375])).

cnf(c_153,plain,
    ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_136])).

cnf(c_32515,plain,
    ( v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) = iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31075,c_149,c_153])).

cnf(c_32516,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0
    | v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_32515])).

cnf(c_100,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f332])).

cnf(c_6036,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100])).

cnf(c_47612,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
    | v4_relat_1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) != iProver_top
    | v1_relat_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_32516,c_6036])).

cnf(c_79,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f311])).

cnf(c_7250,plain,
    ( v4_relat_1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_77,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f310])).

cnf(c_6052,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_12595,plain,
    ( v1_relat_1(sK28) = iProver_top ),
    inference(superposition,[status(thm)],[c_6005,c_6052])).

cnf(c_12618,plain,
    ( v1_relat_1(sK28) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12595])).

cnf(c_47666,plain,
    ( ~ v4_relat_1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))))
    | ~ v1_relat_1(sK28)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_47612])).

cnf(c_71116,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
    inference(global_propositional_subsumption,[status(thm)],[c_47612,c_135,c_7250,c_12618,c_47666])).

cnf(c_85,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k6_partfun1(X2),X0)
    | k2_relset_1(X1,X2,X0) = X2 ),
    inference(cnf_transformation,[],[f400])).

cnf(c_6045,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k6_partfun1(X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85])).

cnf(c_39811,plain,
    ( k2_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))),sK28) = u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | r1_tarski(k6_partfun1(u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))),sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_6005,c_6045])).

cnf(c_82,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f315])).

cnf(c_6048,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82])).

cnf(c_15975,plain,
    ( k2_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))),sK28) = k2_relat_1(sK28) ),
    inference(superposition,[status(thm)],[c_6005,c_6048])).

cnf(c_39846,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28)
    | r1_tarski(k6_partfun1(u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))),sK28) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_39811,c_15975])).

cnf(c_71184,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
    | r1_tarski(k6_partfun1(k1_xboole_0),sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_71116,c_39846])).

cnf(c_70,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f399])).

cnf(c_71411,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
    | r1_tarski(k1_xboole_0,sK28) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_71184,c_70])).

cnf(c_44,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f276])).

cnf(c_18180,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK28))
    | r1_tarski(X0,sK28) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_18187,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK28))
    | r1_tarski(k1_xboole_0,sK28) ),
    inference(instantiation,[status(thm)],[c_18180])).

cnf(c_41,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f273])).

cnf(c_42378,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK28)) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_72362,plain,
    ( ~ r1_tarski(k1_xboole_0,sK28)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_71411])).

cnf(c_75531,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28) ),
    inference(global_propositional_subsumption,[status(thm)],[c_71411,c_18187,c_42378,c_72362])).

cnf(c_75532,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
    inference(renaming,[status(thm)],[c_75531])).

cnf(c_138,negated_conjecture,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) ),
    inference(cnf_transformation,[],[f408])).

cnf(c_6002,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_31076,plain,
    ( u1_struct_0(sK26) = k1_xboole_0
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) != iProver_top
    | v1_partfun1(sK28,u1_struct_0(sK25)) = iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_6002,c_6024])).

cnf(c_139,negated_conjecture,
    ( v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) ),
    inference(cnf_transformation,[],[f409])).

cnf(c_150,plain,
    ( v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_32508,plain,
    ( v1_partfun1(sK28,u1_struct_0(sK25)) = iProver_top
    | u1_struct_0(sK26) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31076,c_149,c_150])).

cnf(c_32509,plain,
    ( u1_struct_0(sK26) = k1_xboole_0
    | v1_partfun1(sK28,u1_struct_0(sK25)) = iProver_top ),
    inference(renaming,[status(thm)],[c_32508])).

cnf(c_47615,plain,
    ( u1_struct_0(sK26) = k1_xboole_0
    | u1_struct_0(sK25) = k1_relat_1(sK28)
    | v4_relat_1(sK28,u1_struct_0(sK25)) != iProver_top
    | v1_relat_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_32509,c_6036])).

cnf(c_7253,plain,
    ( v4_relat_1(sK28,u1_struct_0(sK25))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_47669,plain,
    ( ~ v4_relat_1(sK28,u1_struct_0(sK25))
    | ~ v1_relat_1(sK28)
    | u1_struct_0(sK26) = k1_xboole_0
    | u1_struct_0(sK25) = k1_relat_1(sK28) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_47615])).

cnf(c_54291,plain,
    ( u1_struct_0(sK26) = k1_xboole_0
    | u1_struct_0(sK25) = k1_relat_1(sK28) ),
    inference(global_propositional_subsumption,[status(thm)],[c_47615,c_138,c_7253,c_12618,c_47669])).

cnf(c_129,plain,
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
    inference(cnf_transformation,[],[f431])).

cnf(c_6011,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_129])).

cnf(c_10999,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | v2_pre_topc(sK25) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | l1_pre_topc(sK25) != iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_6005,c_6011])).

cnf(c_144,negated_conjecture,
    ( v2_pre_topc(sK25) ),
    inference(cnf_transformation,[],[f367])).

cnf(c_145,plain,
    ( v2_pre_topc(sK25) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_144])).

cnf(c_143,negated_conjecture,
    ( l1_pre_topc(sK25) ),
    inference(cnf_transformation,[],[f368])).

cnf(c_146,plain,
    ( l1_pre_topc(sK25) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_142,negated_conjecture,
    ( v2_pre_topc(sK26) ),
    inference(cnf_transformation,[],[f369])).

cnf(c_147,plain,
    ( v2_pre_topc(sK26) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_141,negated_conjecture,
    ( l1_pre_topc(sK26) ),
    inference(cnf_transformation,[],[f370])).

cnf(c_148,plain,
    ( l1_pre_topc(sK26) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_125,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f359])).

cnf(c_7078,plain,
    ( m1_subset_1(u1_pre_topc(sK26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK26))))
    | ~ l1_pre_topc(sK26) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_7079,plain,
    ( m1_subset_1(u1_pre_topc(sK26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK26)))) = iProver_top
    | l1_pre_topc(sK26) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7078])).

cnf(c_126,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f360])).

cnf(c_7134,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | ~ v2_pre_topc(sK26)
    | ~ l1_pre_topc(sK26) ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_7135,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
    | v2_pre_topc(sK26) != iProver_top
    | l1_pre_topc(sK26) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7134])).

cnf(c_124,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f358])).

cnf(c_7696,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK26))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_7697,plain,
    ( m1_subset_1(u1_pre_topc(sK26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK26)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7696])).

cnf(c_130,plain,
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
    inference(cnf_transformation,[],[f432])).

cnf(c_6010,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_130])).

cnf(c_9155,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
    | v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | v2_pre_topc(sK25) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | l1_pre_topc(sK25) != iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_6005,c_6010])).

cnf(c_151,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_133,negated_conjecture,
    ( ~ v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | ~ v5_pre_topc(sK28,sK25,sK26) ),
    inference(cnf_transformation,[],[f406])).

cnf(c_156,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | v5_pre_topc(sK28,sK25,sK26) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_131,plain,
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
    inference(cnf_transformation,[],[f433])).

cnf(c_7576,plain,
    ( v5_pre_topc(X0,sK25,X1)
    | ~ v5_pre_topc(X0,sK25,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK25)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK25)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_8429,plain,
    ( ~ v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | v5_pre_topc(sK28,sK25,sK26)
    | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
    | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))
    | ~ v2_pre_topc(sK26)
    | ~ v2_pre_topc(sK25)
    | ~ l1_pre_topc(sK26)
    | ~ l1_pre_topc(sK25)
    | ~ v1_funct_1(sK28) ),
    inference(instantiation,[status(thm)],[c_7576])).

cnf(c_8430,plain,
    ( v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | v5_pre_topc(sK28,sK25,sK26) = iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) != iProver_top
    | v2_pre_topc(sK26) != iProver_top
    | v2_pre_topc(sK25) != iProver_top
    | l1_pre_topc(sK26) != iProver_top
    | l1_pre_topc(sK25) != iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8429])).

cnf(c_9701,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9155,c_145,c_146,c_147,c_148,c_149,c_150,c_151,c_153,c_156,c_7079,c_7135,c_7697,c_8430])).

cnf(c_9702,plain,
    ( v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9701])).

cnf(c_11603,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10999,c_145,c_146,c_147,c_148,c_149,c_150,c_151,c_153,c_156,c_7079,c_7135,c_7697,c_8430,c_9155])).

cnf(c_11604,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11603])).

cnf(c_54401,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_54291,c_11604])).

cnf(c_134,negated_conjecture,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | v5_pre_topc(sK28,sK25,sK26) ),
    inference(cnf_transformation,[],[f407])).

cnf(c_6006,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
    | v5_pre_topc(sK28,sK25,sK26) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134])).

cnf(c_11610,plain,
    ( v5_pre_topc(sK28,sK25,sK26) = iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6006,c_11604])).

cnf(c_132,plain,
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
    inference(cnf_transformation,[],[f434])).

cnf(c_7586,plain,
    ( ~ v5_pre_topc(X0,sK25,X1)
    | v5_pre_topc(X0,sK25,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK25)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK25)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_32011,plain,
    ( v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | ~ v5_pre_topc(sK28,sK25,sK26)
    | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
    | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))
    | ~ v2_pre_topc(sK26)
    | ~ v2_pre_topc(sK25)
    | ~ l1_pre_topc(sK26)
    | ~ l1_pre_topc(sK25)
    | ~ v1_funct_1(sK28) ),
    inference(instantiation,[status(thm)],[c_7586])).

cnf(c_32015,plain,
    ( v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
    | v5_pre_topc(sK28,sK25,sK26) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) != iProver_top
    | v2_pre_topc(sK26) != iProver_top
    | v2_pre_topc(sK25) != iProver_top
    | l1_pre_topc(sK26) != iProver_top
    | l1_pre_topc(sK25) != iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32011])).

cnf(c_57721,plain,
    ( v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_54401,c_145,c_146,c_147,c_148,c_149,c_150,c_151,c_9702,c_11610,c_32015])).

cnf(c_75598,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),k2_relat_1(sK28)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_75532,c_57721])).

cnf(c_373,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_380,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_75596,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
    | k2_relat_1(sK28) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_75532,c_71116])).

cnf(c_84,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f317])).

cnf(c_6046,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(c_42218,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK28),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6002,c_6046])).

cnf(c_90,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f324])).

cnf(c_6040,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_90])).

cnf(c_43709,plain,
    ( v1_funct_2(sK28,u1_struct_0(sK25),X0) = iProver_top
    | v1_partfun1(sK28,u1_struct_0(sK25)) != iProver_top
    | r1_tarski(k2_relat_1(sK28),X0) != iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_42218,c_6040])).

cnf(c_48665,plain,
    ( r1_tarski(k2_relat_1(sK28),X0) != iProver_top
    | v1_partfun1(sK28,u1_struct_0(sK25)) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43709,c_149])).

cnf(c_48666,plain,
    ( v1_funct_2(sK28,u1_struct_0(sK25),X0) = iProver_top
    | v1_partfun1(sK28,u1_struct_0(sK25)) != iProver_top
    | r1_tarski(k2_relat_1(sK28),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_48665])).

cnf(c_57730,plain,
    ( v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_42218,c_57721])).

cnf(c_61034,plain,
    ( v1_partfun1(sK28,u1_struct_0(sK25)) != iProver_top
    | r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_48666,c_57730])).

cnf(c_54410,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_54291,c_6005])).

cnf(c_56605,plain,
    ( k2_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26))),sK28) = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26)))
    | u1_struct_0(sK25) = k1_relat_1(sK28)
    | r1_tarski(k6_partfun1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26)))),sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_54410,c_6045])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,k3_subset_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f394])).

cnf(c_383,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_39,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(cnf_transformation,[],[f423])).

cnf(c_386,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_3489,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8225,plain,
    ( sK28 = sK28 ),
    inference(instantiation,[status(thm)],[c_3489])).

cnf(c_3490,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_11719,plain,
    ( X0 != X1
    | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != X1 ),
    inference(instantiation,[status(thm)],[c_3490])).

cnf(c_11720,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11719])).

cnf(c_18382,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) ),
    inference(instantiation,[status(thm)],[c_3489])).

cnf(c_3495,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_7665,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),X3)
    | X3 != X1
    | k2_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_3495])).

cnf(c_27080,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK28),X2)
    | X2 != X1
    | k2_relat_1(sK28) != X0 ),
    inference(instantiation,[status(thm)],[c_7665])).

cnf(c_27082,plain,
    ( r1_tarski(k2_relat_1(sK28),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_relat_1(sK28) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_27080])).

cnf(c_32517,plain,
    ( v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_32516])).

cnf(c_42217,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK28),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6005,c_6046])).

cnf(c_43950,plain,
    ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),X0) = iProver_top
    | v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) != iProver_top
    | r1_tarski(k2_relat_1(sK28),X0) != iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_42217,c_6040])).

cnf(c_44187,plain,
    ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),X0)
    | ~ v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))))
    | ~ r1_tarski(k2_relat_1(sK28),X0)
    | ~ v1_funct_1(sK28) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_43950])).

cnf(c_44189,plain,
    ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0)
    | ~ v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))))
    | ~ r1_tarski(k2_relat_1(sK28),k1_xboole_0)
    | ~ v1_funct_1(sK28) ),
    inference(instantiation,[status(thm)],[c_44187])).

cnf(c_39812,plain,
    ( k2_relset_1(u1_struct_0(sK25),u1_struct_0(sK26),sK28) = u1_struct_0(sK26)
    | r1_tarski(k6_partfun1(u1_struct_0(sK26)),sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_6002,c_6045])).

cnf(c_15976,plain,
    ( k2_relset_1(u1_struct_0(sK25),u1_struct_0(sK26),sK28) = k2_relat_1(sK28) ),
    inference(superposition,[status(thm)],[c_6002,c_6048])).

cnf(c_39841,plain,
    ( u1_struct_0(sK26) = k2_relat_1(sK28)
    | r1_tarski(k6_partfun1(u1_struct_0(sK26)),sK28) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_39812,c_15976])).

cnf(c_54335,plain,
    ( u1_struct_0(sK26) = k2_relat_1(sK28)
    | u1_struct_0(sK25) = k1_relat_1(sK28)
    | r1_tarski(k6_partfun1(k1_xboole_0),sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_54291,c_39841])).

cnf(c_54907,plain,
    ( u1_struct_0(sK26) = k2_relat_1(sK28)
    | u1_struct_0(sK25) = k1_relat_1(sK28)
    | r1_tarski(k1_xboole_0,sK28) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_54335,c_70])).

cnf(c_55560,plain,
    ( ~ r1_tarski(k1_xboole_0,sK28)
    | u1_struct_0(sK26) = k2_relat_1(sK28)
    | u1_struct_0(sK25) = k1_relat_1(sK28) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_54907])).

cnf(c_58016,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | u1_struct_0(sK26) = k2_relat_1(sK28) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54907,c_18187,c_42378,c_55560])).

cnf(c_58017,plain,
    ( u1_struct_0(sK26) = k2_relat_1(sK28)
    | u1_struct_0(sK25) = k1_relat_1(sK28) ),
    inference(renaming,[status(thm)],[c_58016])).

cnf(c_58051,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | k2_relat_1(sK28) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_58017,c_54291])).

cnf(c_3511,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_7492,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
    | X2 != u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
    | X0 != sK28 ),
    inference(instantiation,[status(thm)],[c_3511])).

cnf(c_8224,plain,
    ( v1_funct_2(sK28,X0,X1)
    | ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
    | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
    | sK28 != sK28 ),
    inference(instantiation,[status(thm)],[c_7492])).

cnf(c_77010,plain,
    ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),X0)
    | ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
    | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
    | sK28 != sK28 ),
    inference(instantiation,[status(thm)],[c_8224])).

cnf(c_77011,plain,
    ( X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
    | sK28 != sK28
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),X0) = iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77010])).

cnf(c_77013,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
    | sK28 != sK28
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77011])).

cnf(c_6009,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_131])).

cnf(c_8764,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) = iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != iProver_top
    | v2_pre_topc(sK26) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != iProver_top
    | l1_pre_topc(sK26) != iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_6005,c_6009])).

cnf(c_7081,plain,
    ( m1_subset_1(u1_pre_topc(sK25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK25))))
    | ~ l1_pre_topc(sK25) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_7082,plain,
    ( m1_subset_1(u1_pre_topc(sK25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK25)))) = iProver_top
    | l1_pre_topc(sK25) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7081])).

cnf(c_7137,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
    | ~ v2_pre_topc(sK25)
    | ~ l1_pre_topc(sK25) ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_7138,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = iProver_top
    | v2_pre_topc(sK25) != iProver_top
    | l1_pre_topc(sK25) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7137])).

cnf(c_7701,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK25))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_7702,plain,
    ( m1_subset_1(u1_pre_topc(sK25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK25)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7701])).

cnf(c_7556,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),X1)
    | v5_pre_topc(X0,sK25,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK25)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK25)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_8422,plain,
    ( ~ v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26)
    | v5_pre_topc(sK28,sK25,sK26)
    | ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26))
    | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26))))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))
    | ~ v2_pre_topc(sK26)
    | ~ v2_pre_topc(sK25)
    | ~ l1_pre_topc(sK26)
    | ~ l1_pre_topc(sK25)
    | ~ v1_funct_1(sK28) ),
    inference(instantiation,[status(thm)],[c_7556])).

cnf(c_8423,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) != iProver_top
    | v5_pre_topc(sK28,sK25,sK26) = iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) != iProver_top
    | v2_pre_topc(sK26) != iProver_top
    | v2_pre_topc(sK25) != iProver_top
    | l1_pre_topc(sK26) != iProver_top
    | l1_pre_topc(sK25) != iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8422])).

cnf(c_9007,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8764,c_145,c_146,c_147,c_148,c_149,c_150,c_151,c_153,c_156,c_7082,c_7138,c_7702,c_8423])).

cnf(c_9008,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9007])).

cnf(c_54406,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_54291,c_9008])).

cnf(c_6008,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_132])).

cnf(c_7805,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
    | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != iProver_top
    | v2_pre_topc(sK26) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != iProver_top
    | l1_pre_topc(sK26) != iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_6005,c_6008])).

cnf(c_8398,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
    | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7805,c_145,c_146,c_147,c_148,c_149,c_153,c_7082,c_7138,c_7702])).

cnf(c_8399,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
    | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8398])).

cnf(c_9014,plain,
    ( v5_pre_topc(sK28,sK25,sK26) = iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6006,c_9008])).

cnf(c_7566,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),X1)
    | ~ v5_pre_topc(X0,sK25,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK25)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK25)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_32012,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26)
    | ~ v5_pre_topc(sK28,sK25,sK26)
    | ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26))
    | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26))))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))
    | ~ v2_pre_topc(sK26)
    | ~ v2_pre_topc(sK25)
    | ~ l1_pre_topc(sK26)
    | ~ l1_pre_topc(sK25)
    | ~ v1_funct_1(sK28) ),
    inference(instantiation,[status(thm)],[c_7566])).

cnf(c_32013,plain,
    ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) = iProver_top
    | v5_pre_topc(sK28,sK25,sK26) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) != iProver_top
    | v2_pre_topc(sK26) != iProver_top
    | v2_pre_topc(sK25) != iProver_top
    | l1_pre_topc(sK26) != iProver_top
    | l1_pre_topc(sK25) != iProver_top
    | v1_funct_1(sK28) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32012])).

cnf(c_61057,plain,
    ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_54406,c_145,c_146,c_147,c_148,c_149,c_150,c_151,c_8399,c_9008,c_9014,c_32013])).

cnf(c_61068,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_54291,c_61057])).

cnf(c_26,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f421])).

cnf(c_61072,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_61068,c_26])).

cnf(c_54412,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_54291,c_6002])).

cnf(c_54420,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | m1_subset_1(sK28,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_54412,c_26])).

cnf(c_82403,plain,
    ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | u1_struct_0(sK25) = k1_relat_1(sK28) ),
    inference(global_propositional_subsumption,[status(thm)],[c_61072,c_54420])).

cnf(c_82404,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top ),
    inference(renaming,[status(thm)],[c_82403])).

cnf(c_82412,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28)
    | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_54291,c_82404])).

cnf(c_82422,plain,
    ( ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0)
    | u1_struct_0(sK25) = k1_relat_1(sK28) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_82412])).

cnf(c_85118,plain,
    ( u1_struct_0(sK25) = k1_relat_1(sK28) ),
    inference(global_propositional_subsumption,[status(thm)],[c_56605,c_140,c_153,c_373,c_380,c_383,c_386,c_8225,c_11720,c_18382,c_27082,c_32517,c_44189,c_58051,c_77013,c_82412,c_82422])).

cnf(c_110368,plain,
    ( v1_partfun1(sK28,k1_relat_1(sK28)) != iProver_top
    | r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_61034,c_85118])).

cnf(c_6078,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_11181,plain,
    ( r1_tarski(sK28,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6005,c_6078])).

cnf(c_101,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f335])).

cnf(c_6035,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_42214,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(k6_partfun1(X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6035,c_6046])).

cnf(c_67,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f396])).

cnf(c_42269,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42214,c_67])).

cnf(c_42583,plain,
    ( k2_relset_1(X0,X1,k6_partfun1(X0)) = k2_relat_1(k6_partfun1(X0))
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_42269,c_6048])).

cnf(c_42586,plain,
    ( k2_relset_1(X0,X1,k6_partfun1(X0)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42583,c_67])).

cnf(c_43161,plain,
    ( k2_relset_1(sK28,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))),k6_partfun1(sK28)) = sK28 ),
    inference(superposition,[status(thm)],[c_11181,c_42586])).

cnf(c_71183,plain,
    ( k2_relset_1(sK28,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0),k6_partfun1(sK28)) = sK28
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
    inference(superposition,[status(thm)],[c_71116,c_43161])).

cnf(c_71417,plain,
    ( k2_relset_1(sK28,k1_xboole_0,k6_partfun1(sK28)) = sK28
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
    inference(demodulation,[status(thm)],[c_71183,c_26])).

cnf(c_73739,plain,
    ( k2_relset_1(sK28,k1_xboole_0,k6_partfun1(sK28)) = sK28
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_71417,c_6005])).

cnf(c_92,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f325])).

cnf(c_6039,plain,
    ( v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_92])).

cnf(c_77432,plain,
    ( k2_relset_1(sK28,k1_xboole_0,k6_partfun1(sK28)) = sK28
    | v1_partfun1(sK28,k1_relat_1(sK28)) = iProver_top
    | v1_xboole_0(k1_relat_1(sK28)) != iProver_top ),
    inference(superposition,[status(thm)],[c_73739,c_6039])).

cnf(c_6051,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_13494,plain,
    ( v4_relat_1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6005,c_6051])).

cnf(c_73733,plain,
    ( k2_relset_1(sK28,k1_xboole_0,k6_partfun1(sK28)) = sK28
    | v4_relat_1(sK28,k1_relat_1(sK28)) = iProver_top ),
    inference(superposition,[status(thm)],[c_71417,c_13494])).

cnf(c_7279,plain,
    ( v4_relat_1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_11408,plain,
    ( v4_relat_1(sK28,k1_relat_1(sK28))
    | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),k2_relat_1(sK28)))) ),
    inference(instantiation,[status(thm)],[c_7279])).

cnf(c_11411,plain,
    ( v4_relat_1(sK28,k1_relat_1(sK28)) = iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),k2_relat_1(sK28)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11408])).

cnf(c_116,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f352])).

cnf(c_22204,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),k2_relat_1(sK28))))
    | ~ v1_funct_1(sK28)
    | ~ v1_relat_1(sK28) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_22205,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),k2_relat_1(sK28)))) = iProver_top
    | v1_funct_1(sK28) != iProver_top
    | v1_relat_1(sK28) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22204])).

cnf(c_77852,plain,
    ( v4_relat_1(sK28,k1_relat_1(sK28)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_73733,c_149,c_11411,c_12595,c_22205])).

cnf(c_99,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v4_relat_1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f429])).

cnf(c_6037,plain,
    ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
    | v4_relat_1(X0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_77858,plain,
    ( v1_partfun1(sK28,k1_relat_1(sK28)) = iProver_top
    | v1_relat_1(sK28) != iProver_top ),
    inference(superposition,[status(thm)],[c_77852,c_6037])).

cnf(c_80077,plain,
    ( v1_partfun1(sK28,k1_relat_1(sK28)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_77432,c_12595,c_77858])).

cnf(c_110371,plain,
    ( r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_110368,c_80077])).

cnf(c_110372,plain,
    ( ~ r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_110371])).

cnf(c_118304,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != X1
    | k2_relat_1(sK28) != X0 ),
    inference(instantiation,[status(thm)],[c_3495])).

cnf(c_118306,plain,
    ( r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != k1_xboole_0
    | k2_relat_1(sK28) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_118304])).

cnf(c_124309,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
    inference(global_propositional_subsumption,[status(thm)],[c_75598,c_373,c_380,c_71116,c_75596,c_110372,c_118306])).

cnf(c_124311,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK28),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
    inference(light_normalisation,[status(thm)],[c_124309,c_85118])).

cnf(c_85162,plain,
    ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(k1_relat_1(sK28),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK28),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_85118,c_61057])).

cnf(c_124319,plain,
    ( v1_funct_2(sK28,k1_relat_1(sK28),u1_struct_0(sK26)) != iProver_top
    | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),u1_struct_0(sK26)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_124311,c_85162])).

cnf(c_6001,plain,
    ( v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_85283,plain,
    ( v1_funct_2(sK28,k1_relat_1(sK28),u1_struct_0(sK26)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_85118,c_6001])).

cnf(c_85282,plain,
    ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),u1_struct_0(sK26)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_85118,c_6002])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_124319,c_85283,c_85282])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 27.84/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.84/4.00  
% 27.84/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.84/4.00  
% 27.84/4.00  ------  iProver source info
% 27.84/4.00  
% 27.84/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.84/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.84/4.00  git: non_committed_changes: false
% 27.84/4.00  git: last_make_outside_of_git: false
% 27.84/4.00  
% 27.84/4.00  ------ 
% 27.84/4.00  
% 27.84/4.00  ------ Input Options
% 27.84/4.00  
% 27.84/4.00  --out_options                           all
% 27.84/4.00  --tptp_safe_out                         true
% 27.84/4.00  --problem_path                          ""
% 27.84/4.00  --include_path                          ""
% 27.84/4.00  --clausifier                            res/vclausify_rel
% 27.84/4.00  --clausifier_options                    --mode clausify
% 27.84/4.00  --stdin                                 false
% 27.84/4.00  --stats_out                             all
% 27.84/4.00  
% 27.84/4.00  ------ General Options
% 27.84/4.00  
% 27.84/4.00  --fof                                   false
% 27.84/4.00  --time_out_real                         305.
% 27.84/4.00  --time_out_virtual                      -1.
% 27.84/4.00  --symbol_type_check                     false
% 27.84/4.00  --clausify_out                          false
% 27.84/4.00  --sig_cnt_out                           false
% 27.84/4.00  --trig_cnt_out                          false
% 27.84/4.00  --trig_cnt_out_tolerance                1.
% 27.84/4.00  --trig_cnt_out_sk_spl                   false
% 27.84/4.00  --abstr_cl_out                          false
% 27.84/4.00  
% 27.84/4.00  ------ Global Options
% 27.84/4.00  
% 27.84/4.00  --schedule                              default
% 27.84/4.00  --add_important_lit                     false
% 27.84/4.00  --prop_solver_per_cl                    1000
% 27.84/4.00  --min_unsat_core                        false
% 27.84/4.00  --soft_assumptions                      false
% 27.84/4.00  --soft_lemma_size                       3
% 27.84/4.00  --prop_impl_unit_size                   0
% 27.84/4.00  --prop_impl_unit                        []
% 27.84/4.00  --share_sel_clauses                     true
% 27.84/4.00  --reset_solvers                         false
% 27.84/4.00  --bc_imp_inh                            [conj_cone]
% 27.84/4.00  --conj_cone_tolerance                   3.
% 27.84/4.00  --extra_neg_conj                        none
% 27.84/4.00  --large_theory_mode                     true
% 27.84/4.00  --prolific_symb_bound                   200
% 27.84/4.00  --lt_threshold                          2000
% 27.84/4.00  --clause_weak_htbl                      true
% 27.84/4.00  --gc_record_bc_elim                     false
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing Options
% 27.84/4.00  
% 27.84/4.00  --preprocessing_flag                    true
% 27.84/4.00  --time_out_prep_mult                    0.1
% 27.84/4.00  --splitting_mode                        input
% 27.84/4.00  --splitting_grd                         true
% 27.84/4.00  --splitting_cvd                         false
% 27.84/4.00  --splitting_cvd_svl                     false
% 27.84/4.00  --splitting_nvd                         32
% 27.84/4.00  --sub_typing                            true
% 27.84/4.00  --prep_gs_sim                           true
% 27.84/4.00  --prep_unflatten                        true
% 27.84/4.00  --prep_res_sim                          true
% 27.84/4.00  --prep_upred                            true
% 27.84/4.00  --prep_sem_filter                       exhaustive
% 27.84/4.00  --prep_sem_filter_out                   false
% 27.84/4.00  --pred_elim                             true
% 27.84/4.00  --res_sim_input                         true
% 27.84/4.00  --eq_ax_congr_red                       true
% 27.84/4.00  --pure_diseq_elim                       true
% 27.84/4.00  --brand_transform                       false
% 27.84/4.00  --non_eq_to_eq                          false
% 27.84/4.00  --prep_def_merge                        true
% 27.84/4.00  --prep_def_merge_prop_impl              false
% 27.84/4.00  --prep_def_merge_mbd                    true
% 27.84/4.00  --prep_def_merge_tr_red                 false
% 27.84/4.00  --prep_def_merge_tr_cl                  false
% 27.84/4.00  --smt_preprocessing                     true
% 27.84/4.00  --smt_ac_axioms                         fast
% 27.84/4.00  --preprocessed_out                      false
% 27.84/4.00  --preprocessed_stats                    false
% 27.84/4.00  
% 27.84/4.00  ------ Abstraction refinement Options
% 27.84/4.00  
% 27.84/4.00  --abstr_ref                             []
% 27.84/4.00  --abstr_ref_prep                        false
% 27.84/4.00  --abstr_ref_until_sat                   false
% 27.84/4.00  --abstr_ref_sig_restrict                funpre
% 27.84/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.84/4.00  --abstr_ref_under                       []
% 27.84/4.00  
% 27.84/4.00  ------ SAT Options
% 27.84/4.00  
% 27.84/4.00  --sat_mode                              false
% 27.84/4.00  --sat_fm_restart_options                ""
% 27.84/4.00  --sat_gr_def                            false
% 27.84/4.00  --sat_epr_types                         true
% 27.84/4.00  --sat_non_cyclic_types                  false
% 27.84/4.00  --sat_finite_models                     false
% 27.84/4.00  --sat_fm_lemmas                         false
% 27.84/4.00  --sat_fm_prep                           false
% 27.84/4.00  --sat_fm_uc_incr                        true
% 27.84/4.00  --sat_out_model                         small
% 27.84/4.00  --sat_out_clauses                       false
% 27.84/4.00  
% 27.84/4.00  ------ QBF Options
% 27.84/4.00  
% 27.84/4.00  --qbf_mode                              false
% 27.84/4.00  --qbf_elim_univ                         false
% 27.84/4.00  --qbf_dom_inst                          none
% 27.84/4.00  --qbf_dom_pre_inst                      false
% 27.84/4.00  --qbf_sk_in                             false
% 27.84/4.00  --qbf_pred_elim                         true
% 27.84/4.00  --qbf_split                             512
% 27.84/4.00  
% 27.84/4.00  ------ BMC1 Options
% 27.84/4.00  
% 27.84/4.00  --bmc1_incremental                      false
% 27.84/4.00  --bmc1_axioms                           reachable_all
% 27.84/4.00  --bmc1_min_bound                        0
% 27.84/4.00  --bmc1_max_bound                        -1
% 27.84/4.00  --bmc1_max_bound_default                -1
% 27.84/4.00  --bmc1_symbol_reachability              true
% 27.84/4.00  --bmc1_property_lemmas                  false
% 27.84/4.00  --bmc1_k_induction                      false
% 27.84/4.00  --bmc1_non_equiv_states                 false
% 27.84/4.00  --bmc1_deadlock                         false
% 27.84/4.00  --bmc1_ucm                              false
% 27.84/4.00  --bmc1_add_unsat_core                   none
% 27.84/4.00  --bmc1_unsat_core_children              false
% 27.84/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.84/4.00  --bmc1_out_stat                         full
% 27.84/4.00  --bmc1_ground_init                      false
% 27.84/4.00  --bmc1_pre_inst_next_state              false
% 27.84/4.00  --bmc1_pre_inst_state                   false
% 27.84/4.00  --bmc1_pre_inst_reach_state             false
% 27.84/4.00  --bmc1_out_unsat_core                   false
% 27.84/4.00  --bmc1_aig_witness_out                  false
% 27.84/4.00  --bmc1_verbose                          false
% 27.84/4.00  --bmc1_dump_clauses_tptp                false
% 27.84/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.84/4.00  --bmc1_dump_file                        -
% 27.84/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.84/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.84/4.00  --bmc1_ucm_extend_mode                  1
% 27.84/4.00  --bmc1_ucm_init_mode                    2
% 27.84/4.00  --bmc1_ucm_cone_mode                    none
% 27.84/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.84/4.00  --bmc1_ucm_relax_model                  4
% 27.84/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.84/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.84/4.00  --bmc1_ucm_layered_model                none
% 27.84/4.00  --bmc1_ucm_max_lemma_size               10
% 27.84/4.00  
% 27.84/4.00  ------ AIG Options
% 27.84/4.00  
% 27.84/4.00  --aig_mode                              false
% 27.84/4.00  
% 27.84/4.00  ------ Instantiation Options
% 27.84/4.00  
% 27.84/4.00  --instantiation_flag                    true
% 27.84/4.00  --inst_sos_flag                         false
% 27.84/4.00  --inst_sos_phase                        true
% 27.84/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.84/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.84/4.00  --inst_lit_sel_side                     num_symb
% 27.84/4.00  --inst_solver_per_active                1400
% 27.84/4.00  --inst_solver_calls_frac                1.
% 27.84/4.00  --inst_passive_queue_type               priority_queues
% 27.84/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.84/4.00  --inst_passive_queues_freq              [25;2]
% 27.84/4.00  --inst_dismatching                      true
% 27.84/4.00  --inst_eager_unprocessed_to_passive     true
% 27.84/4.00  --inst_prop_sim_given                   true
% 27.84/4.00  --inst_prop_sim_new                     false
% 27.84/4.00  --inst_subs_new                         false
% 27.84/4.00  --inst_eq_res_simp                      false
% 27.84/4.00  --inst_subs_given                       false
% 27.84/4.00  --inst_orphan_elimination               true
% 27.84/4.00  --inst_learning_loop_flag               true
% 27.84/4.00  --inst_learning_start                   3000
% 27.84/4.00  --inst_learning_factor                  2
% 27.84/4.00  --inst_start_prop_sim_after_learn       3
% 27.84/4.00  --inst_sel_renew                        solver
% 27.84/4.00  --inst_lit_activity_flag                true
% 27.84/4.00  --inst_restr_to_given                   false
% 27.84/4.00  --inst_activity_threshold               500
% 27.84/4.00  --inst_out_proof                        true
% 27.84/4.00  
% 27.84/4.00  ------ Resolution Options
% 27.84/4.00  
% 27.84/4.00  --resolution_flag                       true
% 27.84/4.00  --res_lit_sel                           adaptive
% 27.84/4.00  --res_lit_sel_side                      none
% 27.84/4.00  --res_ordering                          kbo
% 27.84/4.00  --res_to_prop_solver                    active
% 27.84/4.00  --res_prop_simpl_new                    false
% 27.84/4.00  --res_prop_simpl_given                  true
% 27.84/4.00  --res_passive_queue_type                priority_queues
% 27.84/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.84/4.00  --res_passive_queues_freq               [15;5]
% 27.84/4.00  --res_forward_subs                      full
% 27.84/4.00  --res_backward_subs                     full
% 27.84/4.00  --res_forward_subs_resolution           true
% 27.84/4.00  --res_backward_subs_resolution          true
% 27.84/4.00  --res_orphan_elimination                true
% 27.84/4.00  --res_time_limit                        2.
% 27.84/4.00  --res_out_proof                         true
% 27.84/4.00  
% 27.84/4.00  ------ Superposition Options
% 27.84/4.00  
% 27.84/4.00  --superposition_flag                    true
% 27.84/4.00  --sup_passive_queue_type                priority_queues
% 27.84/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.84/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.84/4.00  --demod_completeness_check              fast
% 27.84/4.00  --demod_use_ground                      true
% 27.84/4.00  --sup_to_prop_solver                    passive
% 27.84/4.00  --sup_prop_simpl_new                    true
% 27.84/4.00  --sup_prop_simpl_given                  true
% 27.84/4.00  --sup_fun_splitting                     false
% 27.84/4.00  --sup_smt_interval                      50000
% 27.84/4.00  
% 27.84/4.00  ------ Superposition Simplification Setup
% 27.84/4.00  
% 27.84/4.00  --sup_indices_passive                   []
% 27.84/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.84/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.84/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.84/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.84/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.84/4.00  --sup_full_bw                           [BwDemod]
% 27.84/4.00  --sup_immed_triv                        [TrivRules]
% 27.84/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.84/4.00  --sup_immed_bw_main                     []
% 27.84/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.84/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.84/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.84/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.84/4.00  
% 27.84/4.00  ------ Combination Options
% 27.84/4.00  
% 27.84/4.00  --comb_res_mult                         3
% 27.84/4.00  --comb_sup_mult                         2
% 27.84/4.00  --comb_inst_mult                        10
% 27.84/4.00  
% 27.84/4.00  ------ Debug Options
% 27.84/4.00  
% 27.84/4.00  --dbg_backtrace                         false
% 27.84/4.00  --dbg_dump_prop_clauses                 false
% 27.84/4.00  --dbg_dump_prop_clauses_file            -
% 27.84/4.00  --dbg_out_stat                          false
% 27.84/4.00  ------ Parsing...
% 27.84/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.84/4.00  ------ Proving...
% 27.84/4.00  ------ Problem Properties 
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  clauses                                 132
% 27.84/4.00  conjectures                             11
% 27.84/4.00  EPR                                     19
% 27.84/4.00  Horn                                    115
% 27.84/4.00  unary                                   40
% 27.84/4.00  binary                                  34
% 27.84/4.00  lits                                    348
% 27.84/4.00  lits eq                                 56
% 27.84/4.00  fd_pure                                 0
% 27.84/4.00  fd_pseudo                               0
% 27.84/4.00  fd_cond                                 9
% 27.84/4.00  fd_pseudo_cond                          13
% 27.84/4.00  AC symbols                              0
% 27.84/4.00  
% 27.84/4.00  ------ Schedule dynamic 5 is on 
% 27.84/4.00  
% 27.84/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  ------ 
% 27.84/4.00  Current options:
% 27.84/4.00  ------ 
% 27.84/4.00  
% 27.84/4.00  ------ Input Options
% 27.84/4.00  
% 27.84/4.00  --out_options                           all
% 27.84/4.00  --tptp_safe_out                         true
% 27.84/4.00  --problem_path                          ""
% 27.84/4.00  --include_path                          ""
% 27.84/4.00  --clausifier                            res/vclausify_rel
% 27.84/4.00  --clausifier_options                    --mode clausify
% 27.84/4.00  --stdin                                 false
% 27.84/4.00  --stats_out                             all
% 27.84/4.00  
% 27.84/4.00  ------ General Options
% 27.84/4.00  
% 27.84/4.00  --fof                                   false
% 27.84/4.00  --time_out_real                         305.
% 27.84/4.00  --time_out_virtual                      -1.
% 27.84/4.00  --symbol_type_check                     false
% 27.84/4.00  --clausify_out                          false
% 27.84/4.00  --sig_cnt_out                           false
% 27.84/4.00  --trig_cnt_out                          false
% 27.84/4.00  --trig_cnt_out_tolerance                1.
% 27.84/4.00  --trig_cnt_out_sk_spl                   false
% 27.84/4.00  --abstr_cl_out                          false
% 27.84/4.00  
% 27.84/4.00  ------ Global Options
% 27.84/4.00  
% 27.84/4.00  --schedule                              default
% 27.84/4.00  --add_important_lit                     false
% 27.84/4.00  --prop_solver_per_cl                    1000
% 27.84/4.00  --min_unsat_core                        false
% 27.84/4.00  --soft_assumptions                      false
% 27.84/4.00  --soft_lemma_size                       3
% 27.84/4.00  --prop_impl_unit_size                   0
% 27.84/4.00  --prop_impl_unit                        []
% 27.84/4.00  --share_sel_clauses                     true
% 27.84/4.00  --reset_solvers                         false
% 27.84/4.00  --bc_imp_inh                            [conj_cone]
% 27.84/4.00  --conj_cone_tolerance                   3.
% 27.84/4.00  --extra_neg_conj                        none
% 27.84/4.00  --large_theory_mode                     true
% 27.84/4.00  --prolific_symb_bound                   200
% 27.84/4.00  --lt_threshold                          2000
% 27.84/4.00  --clause_weak_htbl                      true
% 27.84/4.00  --gc_record_bc_elim                     false
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing Options
% 27.84/4.00  
% 27.84/4.00  --preprocessing_flag                    true
% 27.84/4.00  --time_out_prep_mult                    0.1
% 27.84/4.00  --splitting_mode                        input
% 27.84/4.00  --splitting_grd                         true
% 27.84/4.00  --splitting_cvd                         false
% 27.84/4.00  --splitting_cvd_svl                     false
% 27.84/4.00  --splitting_nvd                         32
% 27.84/4.00  --sub_typing                            true
% 27.84/4.00  --prep_gs_sim                           true
% 27.84/4.00  --prep_unflatten                        true
% 27.84/4.00  --prep_res_sim                          true
% 27.84/4.00  --prep_upred                            true
% 27.84/4.00  --prep_sem_filter                       exhaustive
% 27.84/4.00  --prep_sem_filter_out                   false
% 27.84/4.00  --pred_elim                             true
% 27.84/4.00  --res_sim_input                         true
% 27.84/4.00  --eq_ax_congr_red                       true
% 27.84/4.00  --pure_diseq_elim                       true
% 27.84/4.00  --brand_transform                       false
% 27.84/4.00  --non_eq_to_eq                          false
% 27.84/4.00  --prep_def_merge                        true
% 27.84/4.00  --prep_def_merge_prop_impl              false
% 27.84/4.00  --prep_def_merge_mbd                    true
% 27.84/4.00  --prep_def_merge_tr_red                 false
% 27.84/4.00  --prep_def_merge_tr_cl                  false
% 27.84/4.00  --smt_preprocessing                     true
% 27.84/4.00  --smt_ac_axioms                         fast
% 27.84/4.00  --preprocessed_out                      false
% 27.84/4.00  --preprocessed_stats                    false
% 27.84/4.00  
% 27.84/4.00  ------ Abstraction refinement Options
% 27.84/4.00  
% 27.84/4.00  --abstr_ref                             []
% 27.84/4.00  --abstr_ref_prep                        false
% 27.84/4.00  --abstr_ref_until_sat                   false
% 27.84/4.00  --abstr_ref_sig_restrict                funpre
% 27.84/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.84/4.00  --abstr_ref_under                       []
% 27.84/4.00  
% 27.84/4.00  ------ SAT Options
% 27.84/4.00  
% 27.84/4.00  --sat_mode                              false
% 27.84/4.00  --sat_fm_restart_options                ""
% 27.84/4.00  --sat_gr_def                            false
% 27.84/4.00  --sat_epr_types                         true
% 27.84/4.00  --sat_non_cyclic_types                  false
% 27.84/4.00  --sat_finite_models                     false
% 27.84/4.00  --sat_fm_lemmas                         false
% 27.84/4.00  --sat_fm_prep                           false
% 27.84/4.00  --sat_fm_uc_incr                        true
% 27.84/4.00  --sat_out_model                         small
% 27.84/4.00  --sat_out_clauses                       false
% 27.84/4.00  
% 27.84/4.00  ------ QBF Options
% 27.84/4.00  
% 27.84/4.00  --qbf_mode                              false
% 27.84/4.00  --qbf_elim_univ                         false
% 27.84/4.00  --qbf_dom_inst                          none
% 27.84/4.00  --qbf_dom_pre_inst                      false
% 27.84/4.00  --qbf_sk_in                             false
% 27.84/4.00  --qbf_pred_elim                         true
% 27.84/4.00  --qbf_split                             512
% 27.84/4.00  
% 27.84/4.00  ------ BMC1 Options
% 27.84/4.00  
% 27.84/4.00  --bmc1_incremental                      false
% 27.84/4.00  --bmc1_axioms                           reachable_all
% 27.84/4.00  --bmc1_min_bound                        0
% 27.84/4.00  --bmc1_max_bound                        -1
% 27.84/4.00  --bmc1_max_bound_default                -1
% 27.84/4.00  --bmc1_symbol_reachability              true
% 27.84/4.00  --bmc1_property_lemmas                  false
% 27.84/4.00  --bmc1_k_induction                      false
% 27.84/4.00  --bmc1_non_equiv_states                 false
% 27.84/4.00  --bmc1_deadlock                         false
% 27.84/4.00  --bmc1_ucm                              false
% 27.84/4.00  --bmc1_add_unsat_core                   none
% 27.84/4.00  --bmc1_unsat_core_children              false
% 27.84/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.84/4.00  --bmc1_out_stat                         full
% 27.84/4.00  --bmc1_ground_init                      false
% 27.84/4.00  --bmc1_pre_inst_next_state              false
% 27.84/4.00  --bmc1_pre_inst_state                   false
% 27.84/4.00  --bmc1_pre_inst_reach_state             false
% 27.84/4.00  --bmc1_out_unsat_core                   false
% 27.84/4.00  --bmc1_aig_witness_out                  false
% 27.84/4.00  --bmc1_verbose                          false
% 27.84/4.00  --bmc1_dump_clauses_tptp                false
% 27.84/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.84/4.00  --bmc1_dump_file                        -
% 27.84/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.84/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.84/4.00  --bmc1_ucm_extend_mode                  1
% 27.84/4.00  --bmc1_ucm_init_mode                    2
% 27.84/4.00  --bmc1_ucm_cone_mode                    none
% 27.84/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.84/4.00  --bmc1_ucm_relax_model                  4
% 27.84/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.84/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.84/4.00  --bmc1_ucm_layered_model                none
% 27.84/4.00  --bmc1_ucm_max_lemma_size               10
% 27.84/4.00  
% 27.84/4.00  ------ AIG Options
% 27.84/4.00  
% 27.84/4.00  --aig_mode                              false
% 27.84/4.00  
% 27.84/4.00  ------ Instantiation Options
% 27.84/4.00  
% 27.84/4.00  --instantiation_flag                    true
% 27.84/4.00  --inst_sos_flag                         false
% 27.84/4.00  --inst_sos_phase                        true
% 27.84/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.84/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.84/4.00  --inst_lit_sel_side                     none
% 27.84/4.00  --inst_solver_per_active                1400
% 27.84/4.00  --inst_solver_calls_frac                1.
% 27.84/4.00  --inst_passive_queue_type               priority_queues
% 27.84/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.84/4.00  --inst_passive_queues_freq              [25;2]
% 27.84/4.00  --inst_dismatching                      true
% 27.84/4.00  --inst_eager_unprocessed_to_passive     true
% 27.84/4.00  --inst_prop_sim_given                   true
% 27.84/4.00  --inst_prop_sim_new                     false
% 27.84/4.00  --inst_subs_new                         false
% 27.84/4.00  --inst_eq_res_simp                      false
% 27.84/4.00  --inst_subs_given                       false
% 27.84/4.00  --inst_orphan_elimination               true
% 27.84/4.00  --inst_learning_loop_flag               true
% 27.84/4.00  --inst_learning_start                   3000
% 27.84/4.00  --inst_learning_factor                  2
% 27.84/4.00  --inst_start_prop_sim_after_learn       3
% 27.84/4.00  --inst_sel_renew                        solver
% 27.84/4.00  --inst_lit_activity_flag                true
% 27.84/4.00  --inst_restr_to_given                   false
% 27.84/4.00  --inst_activity_threshold               500
% 27.84/4.00  --inst_out_proof                        true
% 27.84/4.00  
% 27.84/4.00  ------ Resolution Options
% 27.84/4.00  
% 27.84/4.00  --resolution_flag                       false
% 27.84/4.00  --res_lit_sel                           adaptive
% 27.84/4.00  --res_lit_sel_side                      none
% 27.84/4.00  --res_ordering                          kbo
% 27.84/4.00  --res_to_prop_solver                    active
% 27.84/4.00  --res_prop_simpl_new                    false
% 27.84/4.00  --res_prop_simpl_given                  true
% 27.84/4.00  --res_passive_queue_type                priority_queues
% 27.84/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.84/4.00  --res_passive_queues_freq               [15;5]
% 27.84/4.00  --res_forward_subs                      full
% 27.84/4.00  --res_backward_subs                     full
% 27.84/4.00  --res_forward_subs_resolution           true
% 27.84/4.00  --res_backward_subs_resolution          true
% 27.84/4.00  --res_orphan_elimination                true
% 27.84/4.00  --res_time_limit                        2.
% 27.84/4.00  --res_out_proof                         true
% 27.84/4.00  
% 27.84/4.00  ------ Superposition Options
% 27.84/4.00  
% 27.84/4.00  --superposition_flag                    true
% 27.84/4.00  --sup_passive_queue_type                priority_queues
% 27.84/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.84/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.84/4.00  --demod_completeness_check              fast
% 27.84/4.00  --demod_use_ground                      true
% 27.84/4.00  --sup_to_prop_solver                    passive
% 27.84/4.00  --sup_prop_simpl_new                    true
% 27.84/4.00  --sup_prop_simpl_given                  true
% 27.84/4.00  --sup_fun_splitting                     false
% 27.84/4.00  --sup_smt_interval                      50000
% 27.84/4.00  
% 27.84/4.00  ------ Superposition Simplification Setup
% 27.84/4.00  
% 27.84/4.00  --sup_indices_passive                   []
% 27.84/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.84/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.84/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.84/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.84/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.84/4.00  --sup_full_bw                           [BwDemod]
% 27.84/4.00  --sup_immed_triv                        [TrivRules]
% 27.84/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.84/4.00  --sup_immed_bw_main                     []
% 27.84/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.84/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.84/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.84/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.84/4.00  
% 27.84/4.00  ------ Combination Options
% 27.84/4.00  
% 27.84/4.00  --comb_res_mult                         3
% 27.84/4.00  --comb_sup_mult                         2
% 27.84/4.00  --comb_inst_mult                        10
% 27.84/4.00  
% 27.84/4.00  ------ Debug Options
% 27.84/4.00  
% 27.84/4.00  --dbg_backtrace                         false
% 27.84/4.00  --dbg_dump_prop_clauses                 false
% 27.84/4.00  --dbg_dump_prop_clauses_file            -
% 27.84/4.00  --dbg_out_stat                          false
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  ------ Proving...
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  % SZS status Theorem for theBenchmark.p
% 27.84/4.00  
% 27.84/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.84/4.00  
% 27.84/4.00  fof(f80,conjecture,(
% 27.84/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f81,negated_conjecture,(
% 27.84/4.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 27.84/4.00    inference(negated_conjecture,[],[f80])).
% 27.84/4.00  
% 27.84/4.00  fof(f152,plain,(
% 27.84/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 27.84/4.00    inference(ennf_transformation,[],[f81])).
% 27.84/4.00  
% 27.84/4.00  fof(f153,plain,(
% 27.84/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.84/4.00    inference(flattening,[],[f152])).
% 27.84/4.00  
% 27.84/4.00  fof(f216,plain,(
% 27.84/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.84/4.00    inference(nnf_transformation,[],[f153])).
% 27.84/4.00  
% 27.84/4.00  fof(f217,plain,(
% 27.84/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.84/4.00    inference(flattening,[],[f216])).
% 27.84/4.00  
% 27.84/4.00  fof(f221,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK28 = X2 & m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK28))) )),
% 27.84/4.00    introduced(choice_axiom,[])).
% 27.84/4.00  
% 27.84/4.00  fof(f220,plain,(
% 27.84/4.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK27,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK27,X0,X1)) & sK27 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK27,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK27))) )),
% 27.84/4.00    introduced(choice_axiom,[])).
% 27.84/4.00  
% 27.84/4.00  fof(f219,plain,(
% 27.84/4.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) | ~v5_pre_topc(X2,X0,sK26)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) | v5_pre_topc(X2,X0,sK26)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK26)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK26)) & v1_funct_1(X2)) & l1_pre_topc(sK26) & v2_pre_topc(sK26))) )),
% 27.84/4.00    introduced(choice_axiom,[])).
% 27.84/4.00  
% 27.84/4.00  fof(f218,plain,(
% 27.84/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK25,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK25,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK25),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK25) & v2_pre_topc(sK25))),
% 27.84/4.00    introduced(choice_axiom,[])).
% 27.84/4.00  
% 27.84/4.00  fof(f222,plain,(
% 27.84/4.00    ((((~v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) | ~v5_pre_topc(sK27,sK25,sK26)) & (v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) | v5_pre_topc(sK27,sK25,sK26)) & sK27 = sK28 & m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) & v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) & v1_funct_1(sK28)) & m1_subset_1(sK27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) & v1_funct_2(sK27,u1_struct_0(sK25),u1_struct_0(sK26)) & v1_funct_1(sK27)) & l1_pre_topc(sK26) & v2_pre_topc(sK26)) & l1_pre_topc(sK25) & v2_pre_topc(sK25)),
% 27.84/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25,sK26,sK27,sK28])],[f217,f221,f220,f219,f218])).
% 27.84/4.00  
% 27.84/4.00  fof(f376,plain,(
% 27.84/4.00    m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))))),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f70,axiom,(
% 27.84/4.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f134,plain,(
% 27.84/4.00    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 27.84/4.00    inference(ennf_transformation,[],[f70])).
% 27.84/4.00  
% 27.84/4.00  fof(f135,plain,(
% 27.84/4.00    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 27.84/4.00    inference(flattening,[],[f134])).
% 27.84/4.00  
% 27.84/4.00  fof(f348,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f135])).
% 27.84/4.00  
% 27.84/4.00  fof(f371,plain,(
% 27.84/4.00    v1_funct_1(sK27)),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f377,plain,(
% 27.84/4.00    sK27 = sK28),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f410,plain,(
% 27.84/4.00    v1_funct_1(sK28)),
% 27.84/4.00    inference(definition_unfolding,[],[f371,f377])).
% 27.84/4.00  
% 27.84/4.00  fof(f375,plain,(
% 27.84/4.00    v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f65,axiom,(
% 27.84/4.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f132,plain,(
% 27.84/4.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 27.84/4.00    inference(ennf_transformation,[],[f65])).
% 27.84/4.00  
% 27.84/4.00  fof(f133,plain,(
% 27.84/4.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.84/4.00    inference(flattening,[],[f132])).
% 27.84/4.00  
% 27.84/4.00  fof(f205,plain,(
% 27.84/4.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.84/4.00    inference(nnf_transformation,[],[f133])).
% 27.84/4.00  
% 27.84/4.00  fof(f332,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f205])).
% 27.84/4.00  
% 27.84/4.00  fof(f52,axiom,(
% 27.84/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f113,plain,(
% 27.84/4.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.84/4.00    inference(ennf_transformation,[],[f52])).
% 27.84/4.00  
% 27.84/4.00  fof(f311,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f113])).
% 27.84/4.00  
% 27.84/4.00  fof(f51,axiom,(
% 27.84/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f112,plain,(
% 27.84/4.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.84/4.00    inference(ennf_transformation,[],[f51])).
% 27.84/4.00  
% 27.84/4.00  fof(f310,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f112])).
% 27.84/4.00  
% 27.84/4.00  fof(f58,axiom,(
% 27.84/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f120,plain,(
% 27.84/4.00    ! [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2))) | ~r1_tarski(k6_relat_1(X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.84/4.00    inference(ennf_transformation,[],[f58])).
% 27.84/4.00  
% 27.84/4.00  fof(f121,plain,(
% 27.84/4.00    ! [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2))) | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.84/4.00    inference(flattening,[],[f120])).
% 27.84/4.00  
% 27.84/4.00  fof(f319,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f121])).
% 27.84/4.00  
% 27.84/4.00  fof(f69,axiom,(
% 27.84/4.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f347,plain,(
% 27.84/4.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f69])).
% 27.84/4.00  
% 27.84/4.00  fof(f400,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r1_tarski(k6_partfun1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.84/4.00    inference(definition_unfolding,[],[f319,f347])).
% 27.84/4.00  
% 27.84/4.00  fof(f55,axiom,(
% 27.84/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f116,plain,(
% 27.84/4.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.84/4.00    inference(ennf_transformation,[],[f55])).
% 27.84/4.00  
% 27.84/4.00  fof(f315,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f116])).
% 27.84/4.00  
% 27.84/4.00  fof(f46,axiom,(
% 27.84/4.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f303,plain,(
% 27.84/4.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 27.84/4.00    inference(cnf_transformation,[],[f46])).
% 27.84/4.00  
% 27.84/4.00  fof(f399,plain,(
% 27.84/4.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 27.84/4.00    inference(definition_unfolding,[],[f303,f347])).
% 27.84/4.00  
% 27.84/4.00  fof(f31,axiom,(
% 27.84/4.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f183,plain,(
% 27.84/4.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.84/4.00    inference(nnf_transformation,[],[f31])).
% 27.84/4.00  
% 27.84/4.00  fof(f276,plain,(
% 27.84/4.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f183])).
% 27.84/4.00  
% 27.84/4.00  fof(f28,axiom,(
% 27.84/4.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f273,plain,(
% 27.84/4.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f28])).
% 27.84/4.00  
% 27.84/4.00  fof(f373,plain,(
% 27.84/4.00    m1_subset_1(sK27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f408,plain,(
% 27.84/4.00    m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))),
% 27.84/4.00    inference(definition_unfolding,[],[f373,f377])).
% 27.84/4.00  
% 27.84/4.00  fof(f372,plain,(
% 27.84/4.00    v1_funct_2(sK27,u1_struct_0(sK25),u1_struct_0(sK26))),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f409,plain,(
% 27.84/4.00    v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26))),
% 27.84/4.00    inference(definition_unfolding,[],[f372,f377])).
% 27.84/4.00  
% 27.84/4.00  fof(f78,axiom,(
% 27.84/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f148,plain,(
% 27.84/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.84/4.00    inference(ennf_transformation,[],[f78])).
% 27.84/4.00  
% 27.84/4.00  fof(f149,plain,(
% 27.84/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.84/4.00    inference(flattening,[],[f148])).
% 27.84/4.00  
% 27.84/4.00  fof(f214,plain,(
% 27.84/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.84/4.00    inference(nnf_transformation,[],[f149])).
% 27.84/4.00  
% 27.84/4.00  fof(f364,plain,(
% 27.84/4.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f214])).
% 27.84/4.00  
% 27.84/4.00  fof(f431,plain,(
% 27.84/4.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.84/4.00    inference(equality_resolution,[],[f364])).
% 27.84/4.00  
% 27.84/4.00  fof(f367,plain,(
% 27.84/4.00    v2_pre_topc(sK25)),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f368,plain,(
% 27.84/4.00    l1_pre_topc(sK25)),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f369,plain,(
% 27.84/4.00    v2_pre_topc(sK26)),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f370,plain,(
% 27.84/4.00    l1_pre_topc(sK26)),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f75,axiom,(
% 27.84/4.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f143,plain,(
% 27.84/4.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.84/4.00    inference(ennf_transformation,[],[f75])).
% 27.84/4.00  
% 27.84/4.00  fof(f359,plain,(
% 27.84/4.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f143])).
% 27.84/4.00  
% 27.84/4.00  fof(f76,axiom,(
% 27.84/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f83,plain,(
% 27.84/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 27.84/4.00    inference(pure_predicate_removal,[],[f76])).
% 27.84/4.00  
% 27.84/4.00  fof(f144,plain,(
% 27.84/4.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.84/4.00    inference(ennf_transformation,[],[f83])).
% 27.84/4.00  
% 27.84/4.00  fof(f145,plain,(
% 27.84/4.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.84/4.00    inference(flattening,[],[f144])).
% 27.84/4.00  
% 27.84/4.00  fof(f360,plain,(
% 27.84/4.00    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f145])).
% 27.84/4.00  
% 27.84/4.00  fof(f74,axiom,(
% 27.84/4.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f84,plain,(
% 27.84/4.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 27.84/4.00    inference(pure_predicate_removal,[],[f74])).
% 27.84/4.00  
% 27.84/4.00  fof(f142,plain,(
% 27.84/4.00    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 27.84/4.00    inference(ennf_transformation,[],[f84])).
% 27.84/4.00  
% 27.84/4.00  fof(f358,plain,(
% 27.84/4.00    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f142])).
% 27.84/4.00  
% 27.84/4.00  fof(f363,plain,(
% 27.84/4.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f214])).
% 27.84/4.00  
% 27.84/4.00  fof(f432,plain,(
% 27.84/4.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.84/4.00    inference(equality_resolution,[],[f363])).
% 27.84/4.00  
% 27.84/4.00  fof(f379,plain,(
% 27.84/4.00    ~v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) | ~v5_pre_topc(sK27,sK25,sK26)),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f406,plain,(
% 27.84/4.00    ~v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) | ~v5_pre_topc(sK28,sK25,sK26)),
% 27.84/4.00    inference(definition_unfolding,[],[f379,f377])).
% 27.84/4.00  
% 27.84/4.00  fof(f79,axiom,(
% 27.84/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f150,plain,(
% 27.84/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.84/4.00    inference(ennf_transformation,[],[f79])).
% 27.84/4.00  
% 27.84/4.00  fof(f151,plain,(
% 27.84/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.84/4.00    inference(flattening,[],[f150])).
% 27.84/4.00  
% 27.84/4.00  fof(f215,plain,(
% 27.84/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.84/4.00    inference(nnf_transformation,[],[f151])).
% 27.84/4.00  
% 27.84/4.00  fof(f366,plain,(
% 27.84/4.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f215])).
% 27.84/4.00  
% 27.84/4.00  fof(f433,plain,(
% 27.84/4.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.84/4.00    inference(equality_resolution,[],[f366])).
% 27.84/4.00  
% 27.84/4.00  fof(f378,plain,(
% 27.84/4.00    v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) | v5_pre_topc(sK27,sK25,sK26)),
% 27.84/4.00    inference(cnf_transformation,[],[f222])).
% 27.84/4.00  
% 27.84/4.00  fof(f407,plain,(
% 27.84/4.00    v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) | v5_pre_topc(sK28,sK25,sK26)),
% 27.84/4.00    inference(definition_unfolding,[],[f378,f377])).
% 27.84/4.00  
% 27.84/4.00  fof(f365,plain,(
% 27.84/4.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f215])).
% 27.84/4.00  
% 27.84/4.00  fof(f434,plain,(
% 27.84/4.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.84/4.00    inference(equality_resolution,[],[f365])).
% 27.84/4.00  
% 27.84/4.00  fof(f57,axiom,(
% 27.84/4.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f118,plain,(
% 27.84/4.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 27.84/4.00    inference(ennf_transformation,[],[f57])).
% 27.84/4.00  
% 27.84/4.00  fof(f119,plain,(
% 27.84/4.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 27.84/4.00    inference(flattening,[],[f118])).
% 27.84/4.00  
% 27.84/4.00  fof(f317,plain,(
% 27.84/4.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f119])).
% 27.84/4.00  
% 27.84/4.00  fof(f60,axiom,(
% 27.84/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f123,plain,(
% 27.84/4.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.84/4.00    inference(ennf_transformation,[],[f60])).
% 27.84/4.00  
% 27.84/4.00  fof(f124,plain,(
% 27.84/4.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.84/4.00    inference(flattening,[],[f123])).
% 27.84/4.00  
% 27.84/4.00  fof(f324,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f124])).
% 27.84/4.00  
% 27.84/4.00  fof(f27,axiom,(
% 27.84/4.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f93,plain,(
% 27.84/4.00    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.84/4.00    inference(ennf_transformation,[],[f27])).
% 27.84/4.00  
% 27.84/4.00  fof(f182,plain,(
% 27.84/4.00    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.84/4.00    inference(nnf_transformation,[],[f93])).
% 27.84/4.00  
% 27.84/4.00  fof(f271,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f182])).
% 27.84/4.00  
% 27.84/4.00  fof(f21,axiom,(
% 27.84/4.00    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f264,plain,(
% 27.84/4.00    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f21])).
% 27.84/4.00  
% 27.84/4.00  fof(f394,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.84/4.00    inference(definition_unfolding,[],[f271,f264])).
% 27.84/4.00  
% 27.84/4.00  fof(f272,plain,(
% 27.84/4.00    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f182])).
% 27.84/4.00  
% 27.84/4.00  fof(f393,plain,(
% 27.84/4.00    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.84/4.00    inference(definition_unfolding,[],[f272,f264])).
% 27.84/4.00  
% 27.84/4.00  fof(f423,plain,(
% 27.84/4.00    ( ! [X0] : (r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 27.84/4.00    inference(equality_resolution,[],[f393])).
% 27.84/4.00  
% 27.84/4.00  fof(f18,axiom,(
% 27.84/4.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f175,plain,(
% 27.84/4.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 27.84/4.00    inference(nnf_transformation,[],[f18])).
% 27.84/4.00  
% 27.84/4.00  fof(f176,plain,(
% 27.84/4.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 27.84/4.00    inference(flattening,[],[f175])).
% 27.84/4.00  
% 27.84/4.00  fof(f258,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 27.84/4.00    inference(cnf_transformation,[],[f176])).
% 27.84/4.00  
% 27.84/4.00  fof(f421,plain,(
% 27.84/4.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 27.84/4.00    inference(equality_resolution,[],[f258])).
% 27.84/4.00  
% 27.84/4.00  fof(f66,axiom,(
% 27.84/4.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f335,plain,(
% 27.84/4.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f66])).
% 27.84/4.00  
% 27.84/4.00  fof(f44,axiom,(
% 27.84/4.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f301,plain,(
% 27.84/4.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 27.84/4.00    inference(cnf_transformation,[],[f44])).
% 27.84/4.00  
% 27.84/4.00  fof(f396,plain,(
% 27.84/4.00    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 27.84/4.00    inference(definition_unfolding,[],[f301,f347])).
% 27.84/4.00  
% 27.84/4.00  fof(f61,axiom,(
% 27.84/4.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f125,plain,(
% 27.84/4.00    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 27.84/4.00    inference(ennf_transformation,[],[f61])).
% 27.84/4.00  
% 27.84/4.00  fof(f325,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f125])).
% 27.84/4.00  
% 27.84/4.00  fof(f71,axiom,(
% 27.84/4.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f136,plain,(
% 27.84/4.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.84/4.00    inference(ennf_transformation,[],[f71])).
% 27.84/4.00  
% 27.84/4.00  fof(f137,plain,(
% 27.84/4.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.84/4.00    inference(flattening,[],[f136])).
% 27.84/4.00  
% 27.84/4.00  fof(f352,plain,(
% 27.84/4.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f137])).
% 27.84/4.00  
% 27.84/4.00  fof(f333,plain,(
% 27.84/4.00    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f205])).
% 27.84/4.00  
% 27.84/4.00  fof(f429,plain,(
% 27.84/4.00    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 27.84/4.00    inference(equality_resolution,[],[f333])).
% 27.84/4.00  
% 27.84/4.00  cnf(c_135,negated_conjecture,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) ),
% 27.84/4.00      inference(cnf_transformation,[],[f376]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6005,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_135]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_115,plain,
% 27.84/4.00      ( ~ v1_funct_2(X0,X1,X2)
% 27.84/4.00      | v1_partfun1(X0,X1)
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.84/4.00      | ~ v1_funct_1(X0)
% 27.84/4.00      | k1_xboole_0 = X2 ),
% 27.84/4.00      inference(cnf_transformation,[],[f348]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6024,plain,
% 27.84/4.00      ( k1_xboole_0 = X0
% 27.84/4.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 27.84/4.00      | v1_partfun1(X1,X2) = iProver_top
% 27.84/4.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 27.84/4.00      | v1_funct_1(X1) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_115]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_31075,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) = iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6024]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_140,negated_conjecture,
% 27.84/4.00      ( v1_funct_1(sK28) ),
% 27.84/4.00      inference(cnf_transformation,[],[f410]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_149,plain,
% 27.84/4.00      ( v1_funct_1(sK28) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_140]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_136,negated_conjecture,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) ),
% 27.84/4.00      inference(cnf_transformation,[],[f375]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_153,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_136]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32515,plain,
% 27.84/4.00      ( v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) = iProver_top
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0 ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_31075,c_149,c_153]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32516,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0
% 27.84/4.00      | v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) = iProver_top ),
% 27.84/4.00      inference(renaming,[status(thm)],[c_32515]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_100,plain,
% 27.84/4.00      ( ~ v1_partfun1(X0,X1)
% 27.84/4.00      | ~ v4_relat_1(X0,X1)
% 27.84/4.00      | ~ v1_relat_1(X0)
% 27.84/4.00      | k1_relat_1(X0) = X1 ),
% 27.84/4.00      inference(cnf_transformation,[],[f332]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6036,plain,
% 27.84/4.00      ( k1_relat_1(X0) = X1
% 27.84/4.00      | v1_partfun1(X0,X1) != iProver_top
% 27.84/4.00      | v4_relat_1(X0,X1) != iProver_top
% 27.84/4.00      | v1_relat_1(X0) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_100]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_47612,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
% 27.84/4.00      | v4_relat_1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) != iProver_top
% 27.84/4.00      | v1_relat_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_32516,c_6036]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_79,plain,
% 27.84/4.00      ( v4_relat_1(X0,X1)
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 27.84/4.00      inference(cnf_transformation,[],[f311]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7250,plain,
% 27.84/4.00      ( v4_relat_1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_79]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_77,plain,
% 27.84/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.84/4.00      | v1_relat_1(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f310]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6052,plain,
% 27.84/4.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.84/4.00      | v1_relat_1(X0) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_77]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_12595,plain,
% 27.84/4.00      ( v1_relat_1(sK28) = iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6052]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_12618,plain,
% 27.84/4.00      ( v1_relat_1(sK28) ),
% 27.84/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_12595]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_47666,plain,
% 27.84/4.00      ( ~ v4_relat_1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))))
% 27.84/4.00      | ~ v1_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_47612]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_71116,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_47612,c_135,c_7250,c_12618,c_47666]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_85,plain,
% 27.84/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.84/4.00      | ~ r1_tarski(k6_partfun1(X2),X0)
% 27.84/4.00      | k2_relset_1(X1,X2,X0) = X2 ),
% 27.84/4.00      inference(cnf_transformation,[],[f400]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6045,plain,
% 27.84/4.00      ( k2_relset_1(X0,X1,X2) = X1
% 27.84/4.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.84/4.00      | r1_tarski(k6_partfun1(X1),X2) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_85]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_39811,plain,
% 27.84/4.00      ( k2_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))),sK28) = u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | r1_tarski(k6_partfun1(u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))),sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6045]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_82,plain,
% 27.84/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.84/4.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f315]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6048,plain,
% 27.84/4.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 27.84/4.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_82]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15975,plain,
% 27.84/4.00      ( k2_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))),sK28) = k2_relat_1(sK28) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6048]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_39846,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28)
% 27.84/4.00      | r1_tarski(k6_partfun1(u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))),sK28) != iProver_top ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_39811,c_15975]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_71184,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
% 27.84/4.00      | r1_tarski(k6_partfun1(k1_xboole_0),sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_71116,c_39846]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_70,plain,
% 27.84/4.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 27.84/4.00      inference(cnf_transformation,[],[f399]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_71411,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
% 27.84/4.00      | r1_tarski(k1_xboole_0,sK28) != iProver_top ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_71184,c_70]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_44,plain,
% 27.84/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.84/4.00      inference(cnf_transformation,[],[f276]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_18180,plain,
% 27.84/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK28)) | r1_tarski(X0,sK28) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_44]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_18187,plain,
% 27.84/4.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK28))
% 27.84/4.00      | r1_tarski(k1_xboole_0,sK28) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_18180]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41,plain,
% 27.84/4.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 27.84/4.00      inference(cnf_transformation,[],[f273]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42378,plain,
% 27.84/4.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK28)) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_41]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_72362,plain,
% 27.84/4.00      ( ~ r1_tarski(k1_xboole_0,sK28)
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_71411]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_75531,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28) ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_71411,c_18187,c_42378,c_72362]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_75532,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k2_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(renaming,[status(thm)],[c_75531]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_138,negated_conjecture,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) ),
% 27.84/4.00      inference(cnf_transformation,[],[f408]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6002,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_138]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_31076,plain,
% 27.84/4.00      ( u1_struct_0(sK26) = k1_xboole_0
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | v1_partfun1(sK28,u1_struct_0(sK25)) = iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6002,c_6024]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_139,negated_conjecture,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) ),
% 27.84/4.00      inference(cnf_transformation,[],[f409]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_150,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_139]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32508,plain,
% 27.84/4.00      ( v1_partfun1(sK28,u1_struct_0(sK25)) = iProver_top
% 27.84/4.00      | u1_struct_0(sK26) = k1_xboole_0 ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_31076,c_149,c_150]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32509,plain,
% 27.84/4.00      ( u1_struct_0(sK26) = k1_xboole_0
% 27.84/4.00      | v1_partfun1(sK28,u1_struct_0(sK25)) = iProver_top ),
% 27.84/4.00      inference(renaming,[status(thm)],[c_32508]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_47615,plain,
% 27.84/4.00      ( u1_struct_0(sK26) = k1_xboole_0
% 27.84/4.00      | u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | v4_relat_1(sK28,u1_struct_0(sK25)) != iProver_top
% 27.84/4.00      | v1_relat_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_32509,c_6036]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7253,plain,
% 27.84/4.00      ( v4_relat_1(sK28,u1_struct_0(sK25))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_79]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_47669,plain,
% 27.84/4.00      ( ~ v4_relat_1(sK28,u1_struct_0(sK25))
% 27.84/4.00      | ~ v1_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(sK26) = k1_xboole_0
% 27.84/4.00      | u1_struct_0(sK25) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_47615]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_54291,plain,
% 27.84/4.00      ( u1_struct_0(sK26) = k1_xboole_0
% 27.84/4.00      | u1_struct_0(sK25) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_47615,c_138,c_7253,c_12618,c_47669]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_129,plain,
% 27.84/4.00      ( v5_pre_topc(X0,X1,X2)
% 27.84/4.00      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 27.84/4.00      | ~ v2_pre_topc(X1)
% 27.84/4.00      | ~ v2_pre_topc(X2)
% 27.84/4.00      | ~ l1_pre_topc(X1)
% 27.84/4.00      | ~ l1_pre_topc(X2)
% 27.84/4.00      | ~ v1_funct_1(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f431]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6011,plain,
% 27.84/4.00      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 27.84/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 27.84/4.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 27.84/4.00      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 27.84/4.00      | v2_pre_topc(X1) != iProver_top
% 27.84/4.00      | v2_pre_topc(X2) != iProver_top
% 27.84/4.00      | l1_pre_topc(X1) != iProver_top
% 27.84/4.00      | l1_pre_topc(X2) != iProver_top
% 27.84/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_129]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_10999,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
% 27.84/4.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK25) != iProver_top
% 27.84/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK25) != iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6011]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_144,negated_conjecture,
% 27.84/4.00      ( v2_pre_topc(sK25) ),
% 27.84/4.00      inference(cnf_transformation,[],[f367]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_145,plain,
% 27.84/4.00      ( v2_pre_topc(sK25) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_144]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_143,negated_conjecture,
% 27.84/4.00      ( l1_pre_topc(sK25) ),
% 27.84/4.00      inference(cnf_transformation,[],[f368]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_146,plain,
% 27.84/4.00      ( l1_pre_topc(sK25) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_142,negated_conjecture,
% 27.84/4.00      ( v2_pre_topc(sK26) ),
% 27.84/4.00      inference(cnf_transformation,[],[f369]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_147,plain,
% 27.84/4.00      ( v2_pre_topc(sK26) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_142]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_141,negated_conjecture,
% 27.84/4.00      ( l1_pre_topc(sK26) ),
% 27.84/4.00      inference(cnf_transformation,[],[f370]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_148,plain,
% 27.84/4.00      ( l1_pre_topc(sK26) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_141]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_125,plain,
% 27.84/4.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 27.84/4.00      | ~ l1_pre_topc(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f359]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7078,plain,
% 27.84/4.00      ( m1_subset_1(u1_pre_topc(sK26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK26))))
% 27.84/4.00      | ~ l1_pre_topc(sK26) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_125]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7079,plain,
% 27.84/4.00      ( m1_subset_1(u1_pre_topc(sK26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK26)))) = iProver_top
% 27.84/4.00      | l1_pre_topc(sK26) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_7078]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_126,plain,
% 27.84/4.00      ( ~ v2_pre_topc(X0)
% 27.84/4.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 27.84/4.00      | ~ l1_pre_topc(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f360]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7134,plain,
% 27.84/4.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | ~ v2_pre_topc(sK26)
% 27.84/4.00      | ~ l1_pre_topc(sK26) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_126]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7135,plain,
% 27.84/4.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
% 27.84/4.00      | v2_pre_topc(sK26) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK26) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_7134]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_124,plain,
% 27.84/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 27.84/4.00      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 27.84/4.00      inference(cnf_transformation,[],[f358]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7696,plain,
% 27.84/4.00      ( ~ m1_subset_1(u1_pre_topc(sK26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK26))))
% 27.84/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_124]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7697,plain,
% 27.84/4.00      ( m1_subset_1(u1_pre_topc(sK26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_7696]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_130,plain,
% 27.84/4.00      ( ~ v5_pre_topc(X0,X1,X2)
% 27.84/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 27.84/4.00      | ~ v2_pre_topc(X1)
% 27.84/4.00      | ~ v2_pre_topc(X2)
% 27.84/4.00      | ~ l1_pre_topc(X1)
% 27.84/4.00      | ~ l1_pre_topc(X2)
% 27.84/4.00      | ~ v1_funct_1(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f432]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6010,plain,
% 27.84/4.00      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 27.84/4.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 27.84/4.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 27.84/4.00      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 27.84/4.00      | v2_pre_topc(X1) != iProver_top
% 27.84/4.00      | v2_pre_topc(X2) != iProver_top
% 27.84/4.00      | l1_pre_topc(X1) != iProver_top
% 27.84/4.00      | l1_pre_topc(X2) != iProver_top
% 27.84/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_130]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_9155,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
% 27.84/4.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK25) != iProver_top
% 27.84/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK25) != iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6010]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_151,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_138]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_133,negated_conjecture,
% 27.84/4.00      ( ~ v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | ~ v5_pre_topc(sK28,sK25,sK26) ),
% 27.84/4.00      inference(cnf_transformation,[],[f406]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_156,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,sK25,sK26) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_133]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_131,plain,
% 27.84/4.00      ( v5_pre_topc(X0,X1,X2)
% 27.84/4.00      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 27.84/4.00      | ~ v2_pre_topc(X1)
% 27.84/4.00      | ~ v2_pre_topc(X2)
% 27.84/4.00      | ~ l1_pre_topc(X1)
% 27.84/4.00      | ~ l1_pre_topc(X2)
% 27.84/4.00      | ~ v1_funct_1(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f433]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7576,plain,
% 27.84/4.00      ( v5_pre_topc(X0,sK25,X1)
% 27.84/4.00      | ~ v5_pre_topc(X0,sK25,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(X1))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(X1))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 27.84/4.00      | ~ v2_pre_topc(X1)
% 27.84/4.00      | ~ v2_pre_topc(sK25)
% 27.84/4.00      | ~ l1_pre_topc(X1)
% 27.84/4.00      | ~ l1_pre_topc(sK25)
% 27.84/4.00      | ~ v1_funct_1(X0) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_131]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8429,plain,
% 27.84/4.00      ( ~ v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | v5_pre_topc(sK28,sK25,sK26)
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))
% 27.84/4.00      | ~ v2_pre_topc(sK26)
% 27.84/4.00      | ~ v2_pre_topc(sK25)
% 27.84/4.00      | ~ l1_pre_topc(sK26)
% 27.84/4.00      | ~ l1_pre_topc(sK25)
% 27.84/4.00      | ~ v1_funct_1(sK28) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_7576]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8430,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,sK25,sK26) = iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK26) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK25) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK26) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK25) != iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_8429]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_9701,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_9155,c_145,c_146,c_147,c_148,c_149,c_150,c_151,c_153,
% 27.84/4.00                 c_156,c_7079,c_7135,c_7697,c_8430]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_9702,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top ),
% 27.84/4.00      inference(renaming,[status(thm)],[c_9701]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11603,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_10999,c_145,c_146,c_147,c_148,c_149,c_150,c_151,c_153,
% 27.84/4.00                 c_156,c_7079,c_7135,c_7697,c_8430,c_9155]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11604,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top ),
% 27.84/4.00      inference(renaming,[status(thm)],[c_11603]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_54401,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_54291,c_11604]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_134,negated_conjecture,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | v5_pre_topc(sK28,sK25,sK26) ),
% 27.84/4.00      inference(cnf_transformation,[],[f407]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6006,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,sK25,sK26) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_134]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11610,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,sK25,sK26) = iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6006,c_11604]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_132,plain,
% 27.84/4.00      ( ~ v5_pre_topc(X0,X1,X2)
% 27.84/4.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 27.84/4.00      | ~ v2_pre_topc(X1)
% 27.84/4.00      | ~ v2_pre_topc(X2)
% 27.84/4.00      | ~ l1_pre_topc(X1)
% 27.84/4.00      | ~ l1_pre_topc(X2)
% 27.84/4.00      | ~ v1_funct_1(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f434]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7586,plain,
% 27.84/4.00      ( ~ v5_pre_topc(X0,sK25,X1)
% 27.84/4.00      | v5_pre_topc(X0,sK25,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(X1))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(X1))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 27.84/4.00      | ~ v2_pre_topc(X1)
% 27.84/4.00      | ~ v2_pre_topc(sK25)
% 27.84/4.00      | ~ l1_pre_topc(X1)
% 27.84/4.00      | ~ l1_pre_topc(sK25)
% 27.84/4.00      | ~ v1_funct_1(X0) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_132]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32011,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | ~ v5_pre_topc(sK28,sK25,sK26)
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))
% 27.84/4.00      | ~ v2_pre_topc(sK26)
% 27.84/4.00      | ~ v2_pre_topc(sK25)
% 27.84/4.00      | ~ l1_pre_topc(sK26)
% 27.84/4.00      | ~ l1_pre_topc(sK25)
% 27.84/4.00      | ~ v1_funct_1(sK28) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_7586]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32015,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,sK25,g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,sK25,sK26) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK26) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK25) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK26) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK25) != iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_32011]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_57721,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) != iProver_top ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_54401,c_145,c_146,c_147,c_148,c_149,c_150,c_151,
% 27.84/4.00                 c_9702,c_11610,c_32015]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_75598,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),k2_relat_1(sK28)))) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_75532,c_57721]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_373,plain,
% 27.84/4.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 27.84/4.00      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_44]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_380,plain,
% 27.84/4.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_41]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_75596,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28)
% 27.84/4.00      | k2_relat_1(sK28) = k1_xboole_0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_75532,c_71116]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_84,plain,
% 27.84/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 27.84/4.00      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 27.84/4.00      inference(cnf_transformation,[],[f317]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6046,plain,
% 27.84/4.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 27.84/4.00      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_84]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42218,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),X0))) = iProver_top
% 27.84/4.00      | r1_tarski(k2_relat_1(sK28),X0) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6002,c_6046]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_90,plain,
% 27.84/4.00      ( v1_funct_2(X0,X1,X2)
% 27.84/4.00      | ~ v1_partfun1(X0,X1)
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.84/4.00      | ~ v1_funct_1(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f324]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6040,plain,
% 27.84/4.00      ( v1_funct_2(X0,X1,X2) = iProver_top
% 27.84/4.00      | v1_partfun1(X0,X1) != iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.84/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_90]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_43709,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(sK25),X0) = iProver_top
% 27.84/4.00      | v1_partfun1(sK28,u1_struct_0(sK25)) != iProver_top
% 27.84/4.00      | r1_tarski(k2_relat_1(sK28),X0) != iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_42218,c_6040]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_48665,plain,
% 27.84/4.00      ( r1_tarski(k2_relat_1(sK28),X0) != iProver_top
% 27.84/4.00      | v1_partfun1(sK28,u1_struct_0(sK25)) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),X0) = iProver_top ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_43709,c_149]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_48666,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(sK25),X0) = iProver_top
% 27.84/4.00      | v1_partfun1(sK28,u1_struct_0(sK25)) != iProver_top
% 27.84/4.00      | r1_tarski(k2_relat_1(sK28),X0) != iProver_top ),
% 27.84/4.00      inference(renaming,[status(thm)],[c_48665]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_57730,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_42218,c_57721]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_61034,plain,
% 27.84/4.00      ( v1_partfun1(sK28,u1_struct_0(sK25)) != iProver_top
% 27.84/4.00      | r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_48666,c_57730]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_54410,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26)))))) = iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_54291,c_6005]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_56605,plain,
% 27.84/4.00      ( k2_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26))),sK28) = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26)))
% 27.84/4.00      | u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | r1_tarski(k6_partfun1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26)))),sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_54410,c_6045]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_40,plain,
% 27.84/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.84/4.00      | ~ r1_tarski(X0,k3_subset_1(X1,X0))
% 27.84/4.00      | k1_xboole_0 = X0 ),
% 27.84/4.00      inference(cnf_transformation,[],[f394]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_383,plain,
% 27.84/4.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 27.84/4.00      | ~ r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0))
% 27.84/4.00      | k1_xboole_0 = k1_xboole_0 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_40]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_39,plain,
% 27.84/4.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 27.84/4.00      | r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
% 27.84/4.00      inference(cnf_transformation,[],[f423]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_386,plain,
% 27.84/4.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 27.84/4.00      | r1_tarski(k1_xboole_0,k3_subset_1(k1_xboole_0,k1_xboole_0)) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_39]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3489,plain,( X0 = X0 ),theory(equality) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8225,plain,
% 27.84/4.00      ( sK28 = sK28 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_3489]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3490,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11719,plain,
% 27.84/4.00      ( X0 != X1
% 27.84/4.00      | X0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != X1 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_3490]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11720,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != k1_xboole_0
% 27.84/4.00      | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | k1_xboole_0 != k1_xboole_0 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_11719]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_18382,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_3489]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3495,plain,
% 27.84/4.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.84/4.00      theory(equality) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7665,plain,
% 27.84/4.00      ( ~ r1_tarski(X0,X1)
% 27.84/4.00      | r1_tarski(k2_relat_1(X2),X3)
% 27.84/4.00      | X3 != X1
% 27.84/4.00      | k2_relat_1(X2) != X0 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_3495]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_27080,plain,
% 27.84/4.00      ( ~ r1_tarski(X0,X1)
% 27.84/4.00      | r1_tarski(k2_relat_1(sK28),X2)
% 27.84/4.00      | X2 != X1
% 27.84/4.00      | k2_relat_1(sK28) != X0 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_7665]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_27082,plain,
% 27.84/4.00      ( r1_tarski(k2_relat_1(sK28),k1_xboole_0)
% 27.84/4.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 27.84/4.00      | k2_relat_1(sK28) != k1_xboole_0
% 27.84/4.00      | k1_xboole_0 != k1_xboole_0 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_27080]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32517,plain,
% 27.84/4.00      ( v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))))
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = k1_xboole_0 ),
% 27.84/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_32516]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42217,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),X0))) = iProver_top
% 27.84/4.00      | r1_tarski(k2_relat_1(sK28),X0) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6046]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_43950,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),X0) = iProver_top
% 27.84/4.00      | v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) != iProver_top
% 27.84/4.00      | r1_tarski(k2_relat_1(sK28),X0) != iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_42217,c_6040]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_44187,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),X0)
% 27.84/4.00      | ~ v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))))
% 27.84/4.00      | ~ r1_tarski(k2_relat_1(sK28),X0)
% 27.84/4.00      | ~ v1_funct_1(sK28) ),
% 27.84/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_43950]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_44189,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0)
% 27.84/4.00      | ~ v1_partfun1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))))
% 27.84/4.00      | ~ r1_tarski(k2_relat_1(sK28),k1_xboole_0)
% 27.84/4.00      | ~ v1_funct_1(sK28) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_44187]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_39812,plain,
% 27.84/4.00      ( k2_relset_1(u1_struct_0(sK25),u1_struct_0(sK26),sK28) = u1_struct_0(sK26)
% 27.84/4.00      | r1_tarski(k6_partfun1(u1_struct_0(sK26)),sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6002,c_6045]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15976,plain,
% 27.84/4.00      ( k2_relset_1(u1_struct_0(sK25),u1_struct_0(sK26),sK28) = k2_relat_1(sK28) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6002,c_6048]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_39841,plain,
% 27.84/4.00      ( u1_struct_0(sK26) = k2_relat_1(sK28)
% 27.84/4.00      | r1_tarski(k6_partfun1(u1_struct_0(sK26)),sK28) != iProver_top ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_39812,c_15976]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_54335,plain,
% 27.84/4.00      ( u1_struct_0(sK26) = k2_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | r1_tarski(k6_partfun1(k1_xboole_0),sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_54291,c_39841]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_54907,plain,
% 27.84/4.00      ( u1_struct_0(sK26) = k2_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | r1_tarski(k1_xboole_0,sK28) != iProver_top ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_54335,c_70]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_55560,plain,
% 27.84/4.00      ( ~ r1_tarski(k1_xboole_0,sK28)
% 27.84/4.00      | u1_struct_0(sK26) = k2_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(sK25) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_54907]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_58016,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(sK26) = k2_relat_1(sK28) ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_54907,c_18187,c_42378,c_55560]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_58017,plain,
% 27.84/4.00      ( u1_struct_0(sK26) = k2_relat_1(sK28)
% 27.84/4.00      | u1_struct_0(sK25) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(renaming,[status(thm)],[c_58016]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_58051,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | k2_relat_1(sK28) = k1_xboole_0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_58017,c_54291]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3511,plain,
% 27.84/4.00      ( ~ v1_funct_2(X0,X1,X2)
% 27.84/4.00      | v1_funct_2(X3,X4,X5)
% 27.84/4.00      | X3 != X0
% 27.84/4.00      | X4 != X1
% 27.84/4.00      | X5 != X2 ),
% 27.84/4.00      theory(equality) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7492,plain,
% 27.84/4.00      ( v1_funct_2(X0,X1,X2)
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
% 27.84/4.00      | X2 != u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
% 27.84/4.00      | X0 != sK28 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_3511]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8224,plain,
% 27.84/4.00      ( v1_funct_2(sK28,X0,X1)
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
% 27.84/4.00      | X1 != u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
% 27.84/4.00      | sK28 != sK28 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_7492]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_77010,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),X0)
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
% 27.84/4.00      | X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
% 27.84/4.00      | sK28 != sK28 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_8224]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_77011,plain,
% 27.84/4.00      ( X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
% 27.84/4.00      | sK28 != sK28
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),X0) = iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_77010]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_77013,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
% 27.84/4.00      | sK28 != sK28
% 27.84/4.00      | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0) = iProver_top ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_77011]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6009,plain,
% 27.84/4.00      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 27.84/4.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 27.84/4.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 27.84/4.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 27.84/4.00      | v2_pre_topc(X1) != iProver_top
% 27.84/4.00      | v2_pre_topc(X2) != iProver_top
% 27.84/4.00      | l1_pre_topc(X1) != iProver_top
% 27.84/4.00      | l1_pre_topc(X2) != iProver_top
% 27.84/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_131]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8764,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) = iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK26) != iProver_top
% 27.84/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK26) != iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6009]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7081,plain,
% 27.84/4.00      ( m1_subset_1(u1_pre_topc(sK25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK25))))
% 27.84/4.00      | ~ l1_pre_topc(sK25) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_125]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7082,plain,
% 27.84/4.00      ( m1_subset_1(u1_pre_topc(sK25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK25)))) = iProver_top
% 27.84/4.00      | l1_pre_topc(sK25) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_7081]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7137,plain,
% 27.84/4.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))
% 27.84/4.00      | ~ v2_pre_topc(sK25)
% 27.84/4.00      | ~ l1_pre_topc(sK25) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_126]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7138,plain,
% 27.84/4.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = iProver_top
% 27.84/4.00      | v2_pre_topc(sK25) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK25) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_7137]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7701,plain,
% 27.84/4.00      ( ~ m1_subset_1(u1_pre_topc(sK25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK25))))
% 27.84/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_124]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7702,plain,
% 27.84/4.00      ( m1_subset_1(u1_pre_topc(sK25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK25)))) != iProver_top
% 27.84/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_7701]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7556,plain,
% 27.84/4.00      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),X1)
% 27.84/4.00      | v5_pre_topc(X0,sK25,X1)
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(X1))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(X1))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(X1))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(X1))))
% 27.84/4.00      | ~ v2_pre_topc(X1)
% 27.84/4.00      | ~ v2_pre_topc(sK25)
% 27.84/4.00      | ~ l1_pre_topc(X1)
% 27.84/4.00      | ~ l1_pre_topc(sK25)
% 27.84/4.00      | ~ v1_funct_1(X0) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_129]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8422,plain,
% 27.84/4.00      ( ~ v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26)
% 27.84/4.00      | v5_pre_topc(sK28,sK25,sK26)
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26))
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26))))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))
% 27.84/4.00      | ~ v2_pre_topc(sK26)
% 27.84/4.00      | ~ v2_pre_topc(sK25)
% 27.84/4.00      | ~ l1_pre_topc(sK26)
% 27.84/4.00      | ~ l1_pre_topc(sK25)
% 27.84/4.00      | ~ v1_funct_1(sK28) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_7556]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8423,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) != iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,sK25,sK26) = iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK26) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK25) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK26) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK25) != iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_8422]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_9007,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_8764,c_145,c_146,c_147,c_148,c_149,c_150,c_151,c_153,
% 27.84/4.00                 c_156,c_7082,c_7138,c_7702,c_8423]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_9008,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
% 27.84/4.00      inference(renaming,[status(thm)],[c_9007]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_54406,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK26))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_54291,c_9008]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6008,plain,
% 27.84/4.00      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 27.84/4.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 27.84/4.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 27.84/4.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 27.84/4.00      | v2_pre_topc(X1) != iProver_top
% 27.84/4.00      | v2_pre_topc(X2) != iProver_top
% 27.84/4.00      | l1_pre_topc(X1) != iProver_top
% 27.84/4.00      | l1_pre_topc(X2) != iProver_top
% 27.84/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_132]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7805,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK26) != iProver_top
% 27.84/4.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK26) != iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6008]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8398,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) != iProver_top ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_7805,c_145,c_146,c_147,c_148,c_149,c_153,c_7082,
% 27.84/4.00                 c_7138,c_7702]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8399,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) = iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
% 27.84/4.00      inference(renaming,[status(thm)],[c_8398]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_9014,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,sK25,sK26) = iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6006,c_9008]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7566,plain,
% 27.84/4.00      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),X1)
% 27.84/4.00      | ~ v5_pre_topc(X0,sK25,X1)
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(X1))
% 27.84/4.00      | ~ v1_funct_2(X0,u1_struct_0(sK25),u1_struct_0(X1))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(X1))))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(X1))))
% 27.84/4.00      | ~ v2_pre_topc(X1)
% 27.84/4.00      | ~ v2_pre_topc(sK25)
% 27.84/4.00      | ~ l1_pre_topc(X1)
% 27.84/4.00      | ~ l1_pre_topc(sK25)
% 27.84/4.00      | ~ v1_funct_1(X0) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_130]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32012,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26)
% 27.84/4.00      | ~ v5_pre_topc(sK28,sK25,sK26)
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26))
% 27.84/4.00      | ~ v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26))))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26))))
% 27.84/4.00      | ~ v2_pre_topc(sK26)
% 27.84/4.00      | ~ v2_pre_topc(sK25)
% 27.84/4.00      | ~ l1_pre_topc(sK26)
% 27.84/4.00      | ~ l1_pre_topc(sK25)
% 27.84/4.00      | ~ v1_funct_1(sK28) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_7566]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32013,plain,
% 27.84/4.00      ( v5_pre_topc(sK28,g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)),sK26) = iProver_top
% 27.84/4.00      | v5_pre_topc(sK28,sK25,sK26) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),u1_struct_0(sK26)))) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK26) != iProver_top
% 27.84/4.00      | v2_pre_topc(sK25) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK26) != iProver_top
% 27.84/4.00      | l1_pre_topc(sK25) != iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_32012]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_61057,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_54406,c_145,c_146,c_147,c_148,c_149,c_150,c_151,
% 27.84/4.00                 c_8399,c_9008,c_9014,c_32013]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_61068,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0))) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_54291,c_61057]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_26,plain,
% 27.84/4.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 27.84/4.00      inference(cnf_transformation,[],[f421]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_61072,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_61068,c_26]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_54412,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK25),k1_xboole_0))) = iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_54291,c_6002]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_54420,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_54412,c_26]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_82403,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | u1_struct_0(sK25) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_61072,c_54420]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_82404,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top ),
% 27.84/4.00      inference(renaming,[status(thm)],[c_82403]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_82412,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28)
% 27.84/4.00      | v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_54291,c_82404]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_82422,plain,
% 27.84/4.00      ( ~ v1_funct_2(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0)
% 27.84/4.00      | u1_struct_0(sK25) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_82412]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_85118,plain,
% 27.84/4.00      ( u1_struct_0(sK25) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_56605,c_140,c_153,c_373,c_380,c_383,c_386,c_8225,
% 27.84/4.00                 c_11720,c_18382,c_27082,c_32517,c_44189,c_58051,c_77013,
% 27.84/4.00                 c_82412,c_82422]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_110368,plain,
% 27.84/4.00      ( v1_partfun1(sK28,k1_relat_1(sK28)) != iProver_top
% 27.84/4.00      | r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_61034,c_85118]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6078,plain,
% 27.84/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.84/4.00      | r1_tarski(X0,X1) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11181,plain,
% 27.84/4.00      ( r1_tarski(sK28,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))) = iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6078]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_101,plain,
% 27.84/4.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 27.84/4.00      inference(cnf_transformation,[],[f335]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6035,plain,
% 27.84/4.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42214,plain,
% 27.84/4.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 27.84/4.00      | r1_tarski(k2_relat_1(k6_partfun1(X0)),X1) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6035,c_6046]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_67,plain,
% 27.84/4.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 27.84/4.00      inference(cnf_transformation,[],[f396]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42269,plain,
% 27.84/4.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 27.84/4.00      | r1_tarski(X0,X1) != iProver_top ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_42214,c_67]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42583,plain,
% 27.84/4.00      ( k2_relset_1(X0,X1,k6_partfun1(X0)) = k2_relat_1(k6_partfun1(X0))
% 27.84/4.00      | r1_tarski(X0,X1) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_42269,c_6048]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42586,plain,
% 27.84/4.00      ( k2_relset_1(X0,X1,k6_partfun1(X0)) = X0
% 27.84/4.00      | r1_tarski(X0,X1) != iProver_top ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_42583,c_67]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_43161,plain,
% 27.84/4.00      ( k2_relset_1(sK28,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))),k6_partfun1(sK28)) = sK28 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_11181,c_42586]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_71183,plain,
% 27.84/4.00      ( k2_relset_1(sK28,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))),k1_xboole_0),k6_partfun1(sK28)) = sK28
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_71116,c_43161]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_71417,plain,
% 27.84/4.00      ( k2_relset_1(sK28,k1_xboole_0,k6_partfun1(sK28)) = sK28
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_71183,c_26]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_73739,plain,
% 27.84/4.00      ( k2_relset_1(sK28,k1_xboole_0,k6_partfun1(sK28)) = sK28
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))))) = iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_71417,c_6005]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_92,plain,
% 27.84/4.00      ( v1_partfun1(X0,X1)
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.84/4.00      | ~ v1_xboole_0(X1) ),
% 27.84/4.00      inference(cnf_transformation,[],[f325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6039,plain,
% 27.84/4.00      ( v1_partfun1(X0,X1) = iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.84/4.00      | v1_xboole_0(X1) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_92]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_77432,plain,
% 27.84/4.00      ( k2_relset_1(sK28,k1_xboole_0,k6_partfun1(sK28)) = sK28
% 27.84/4.00      | v1_partfun1(sK28,k1_relat_1(sK28)) = iProver_top
% 27.84/4.00      | v1_xboole_0(k1_relat_1(sK28)) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_73739,c_6039]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6051,plain,
% 27.84/4.00      ( v4_relat_1(X0,X1) = iProver_top
% 27.84/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_79]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13494,plain,
% 27.84/4.00      ( v4_relat_1(sK28,u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25)))) = iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6005,c_6051]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_73733,plain,
% 27.84/4.00      ( k2_relset_1(sK28,k1_xboole_0,k6_partfun1(sK28)) = sK28
% 27.84/4.00      | v4_relat_1(sK28,k1_relat_1(sK28)) = iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_71417,c_13494]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7279,plain,
% 27.84/4.00      ( v4_relat_1(X0,k1_relat_1(X0))
% 27.84/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_79]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11408,plain,
% 27.84/4.00      ( v4_relat_1(sK28,k1_relat_1(sK28))
% 27.84/4.00      | ~ m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),k2_relat_1(sK28)))) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_7279]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11411,plain,
% 27.84/4.00      ( v4_relat_1(sK28,k1_relat_1(sK28)) = iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),k2_relat_1(sK28)))) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_11408]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_116,plain,
% 27.84/4.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 27.84/4.00      | ~ v1_funct_1(X0)
% 27.84/4.00      | ~ v1_relat_1(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f352]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_22204,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),k2_relat_1(sK28))))
% 27.84/4.00      | ~ v1_funct_1(sK28)
% 27.84/4.00      | ~ v1_relat_1(sK28) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_116]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_22205,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),k2_relat_1(sK28)))) = iProver_top
% 27.84/4.00      | v1_funct_1(sK28) != iProver_top
% 27.84/4.00      | v1_relat_1(sK28) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_22204]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_77852,plain,
% 27.84/4.00      ( v4_relat_1(sK28,k1_relat_1(sK28)) = iProver_top ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_73733,c_149,c_11411,c_12595,c_22205]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_99,plain,
% 27.84/4.00      ( v1_partfun1(X0,k1_relat_1(X0))
% 27.84/4.00      | ~ v4_relat_1(X0,k1_relat_1(X0))
% 27.84/4.00      | ~ v1_relat_1(X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f429]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6037,plain,
% 27.84/4.00      ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
% 27.84/4.00      | v4_relat_1(X0,k1_relat_1(X0)) != iProver_top
% 27.84/4.00      | v1_relat_1(X0) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_99]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_77858,plain,
% 27.84/4.00      ( v1_partfun1(sK28,k1_relat_1(sK28)) = iProver_top
% 27.84/4.00      | v1_relat_1(sK28) != iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_77852,c_6037]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_80077,plain,
% 27.84/4.00      ( v1_partfun1(sK28,k1_relat_1(sK28)) = iProver_top ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_77432,c_12595,c_77858]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_110371,plain,
% 27.84/4.00      ( r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) != iProver_top ),
% 27.84/4.00      inference(forward_subsumption_resolution,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_110368,c_80077]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_110372,plain,
% 27.84/4.00      ( ~ r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26)))) ),
% 27.84/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_110371]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_118304,plain,
% 27.84/4.00      ( ~ r1_tarski(X0,X1)
% 27.84/4.00      | r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != X1
% 27.84/4.00      | k2_relat_1(sK28) != X0 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_3495]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_118306,plain,
% 27.84/4.00      ( r1_tarski(k2_relat_1(sK28),u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))))
% 27.84/4.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 27.84/4.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK26),u1_pre_topc(sK26))) != k1_xboole_0
% 27.84/4.00      | k2_relat_1(sK28) != k1_xboole_0 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_118304]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_124309,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK25),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_75598,c_373,c_380,c_71116,c_75596,c_110372,c_118306]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_124311,plain,
% 27.84/4.00      ( u1_struct_0(g1_pre_topc(k1_relat_1(sK28),u1_pre_topc(sK25))) = k1_relat_1(sK28) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_124309,c_85118]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_85162,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(g1_pre_topc(k1_relat_1(sK28),u1_pre_topc(sK25))),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK28),u1_pre_topc(sK25))),u1_struct_0(sK26)))) != iProver_top ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_85118,c_61057]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_124319,plain,
% 27.84/4.00      ( v1_funct_2(sK28,k1_relat_1(sK28),u1_struct_0(sK26)) != iProver_top
% 27.84/4.00      | m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),u1_struct_0(sK26)))) != iProver_top ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_124311,c_85162]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6001,plain,
% 27.84/4.00      ( v1_funct_2(sK28,u1_struct_0(sK25),u1_struct_0(sK26)) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_139]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_85283,plain,
% 27.84/4.00      ( v1_funct_2(sK28,k1_relat_1(sK28),u1_struct_0(sK26)) = iProver_top ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_85118,c_6001]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_85282,plain,
% 27.84/4.00      ( m1_subset_1(sK28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK28),u1_struct_0(sK26)))) = iProver_top ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_85118,c_6002]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(contradiction,plain,
% 27.84/4.00      ( $false ),
% 27.84/4.00      inference(minisat,[status(thm)],[c_124319,c_85283,c_85282]) ).
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.84/4.00  
% 27.84/4.00  ------                               Statistics
% 27.84/4.00  
% 27.84/4.00  ------ General
% 27.84/4.00  
% 27.84/4.00  abstr_ref_over_cycles:                  0
% 27.84/4.00  abstr_ref_under_cycles:                 0
% 27.84/4.00  gc_basic_clause_elim:                   0
% 27.84/4.00  forced_gc_time:                         0
% 27.84/4.00  parsing_time:                           0.022
% 27.84/4.00  unif_index_cands_time:                  0.
% 27.84/4.00  unif_index_add_time:                    0.
% 27.84/4.00  orderings_time:                         0.
% 27.84/4.00  out_proof_time:                         0.053
% 27.84/4.00  total_time:                             3.4
% 27.84/4.00  num_of_symbols:                         99
% 27.84/4.00  num_of_terms:                           107929
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing
% 27.84/4.00  
% 27.84/4.00  num_of_splits:                          0
% 27.84/4.00  num_of_split_atoms:                     0
% 27.84/4.00  num_of_reused_defs:                     0
% 27.84/4.00  num_eq_ax_congr_red:                    210
% 27.84/4.00  num_of_sem_filtered_clauses:            1
% 27.84/4.00  num_of_subtypes:                        0
% 27.84/4.00  monotx_restored_types:                  0
% 27.84/4.00  sat_num_of_epr_types:                   0
% 27.84/4.00  sat_num_of_non_cyclic_types:            0
% 27.84/4.00  sat_guarded_non_collapsed_types:        0
% 27.84/4.00  num_pure_diseq_elim:                    0
% 27.84/4.00  simp_replaced_by:                       0
% 27.84/4.00  res_preprocessed:                       597
% 27.84/4.00  prep_upred:                             0
% 27.84/4.00  prep_unflattend:                        55
% 27.84/4.00  smt_new_axioms:                         0
% 27.84/4.00  pred_elim_cands:                        14
% 27.84/4.00  pred_elim:                              3
% 27.84/4.00  pred_elim_cl:                           6
% 27.84/4.00  pred_elim_cycles:                       9
% 27.84/4.00  merged_defs:                            24
% 27.84/4.00  merged_defs_ncl:                        0
% 27.84/4.00  bin_hyper_res:                          27
% 27.84/4.00  prep_cycles:                            4
% 27.84/4.00  pred_elim_time:                         0.012
% 27.84/4.00  splitting_time:                         0.
% 27.84/4.00  sem_filter_time:                        0.
% 27.84/4.00  monotx_time:                            0.001
% 27.84/4.00  subtype_inf_time:                       0.
% 27.84/4.00  
% 27.84/4.00  ------ Problem properties
% 27.84/4.00  
% 27.84/4.00  clauses:                                132
% 27.84/4.00  conjectures:                            11
% 27.84/4.00  epr:                                    19
% 27.84/4.00  horn:                                   115
% 27.84/4.00  ground:                                 17
% 27.84/4.00  unary:                                  40
% 27.84/4.00  binary:                                 34
% 27.84/4.00  lits:                                   348
% 27.84/4.00  lits_eq:                                56
% 27.84/4.00  fd_pure:                                0
% 27.84/4.00  fd_pseudo:                              0
% 27.84/4.00  fd_cond:                                9
% 27.84/4.00  fd_pseudo_cond:                         13
% 27.84/4.00  ac_symbols:                             0
% 27.84/4.00  
% 27.84/4.00  ------ Propositional Solver
% 27.84/4.00  
% 27.84/4.00  prop_solver_calls:                      43
% 27.84/4.00  prop_fast_solver_calls:                 6330
% 27.84/4.00  smt_solver_calls:                       0
% 27.84/4.00  smt_fast_solver_calls:                  0
% 27.84/4.00  prop_num_of_clauses:                    39996
% 27.84/4.00  prop_preprocess_simplified:             78750
% 27.84/4.00  prop_fo_subsumed:                       315
% 27.84/4.00  prop_solver_time:                       0.
% 27.84/4.00  smt_solver_time:                        0.
% 27.84/4.00  smt_fast_solver_time:                   0.
% 27.84/4.00  prop_fast_solver_time:                  0.
% 27.84/4.00  prop_unsat_core_time:                   0.004
% 27.84/4.00  
% 27.84/4.00  ------ QBF
% 27.84/4.00  
% 27.84/4.00  qbf_q_res:                              0
% 27.84/4.00  qbf_num_tautologies:                    0
% 27.84/4.00  qbf_prep_cycles:                        0
% 27.84/4.00  
% 27.84/4.00  ------ BMC1
% 27.84/4.00  
% 27.84/4.00  bmc1_current_bound:                     -1
% 27.84/4.00  bmc1_last_solved_bound:                 -1
% 27.84/4.00  bmc1_unsat_core_size:                   -1
% 27.84/4.00  bmc1_unsat_core_parents_size:           -1
% 27.84/4.00  bmc1_merge_next_fun:                    0
% 27.84/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.84/4.00  
% 27.84/4.00  ------ Instantiation
% 27.84/4.00  
% 27.84/4.00  inst_num_of_clauses:                    915
% 27.84/4.00  inst_num_in_passive:                    309
% 27.84/4.00  inst_num_in_active:                     2329
% 27.84/4.00  inst_num_in_unprocessed:                247
% 27.84/4.00  inst_num_of_loops:                      3399
% 27.84/4.00  inst_num_of_learning_restarts:          1
% 27.84/4.00  inst_num_moves_active_passive:          1067
% 27.84/4.00  inst_lit_activity:                      0
% 27.84/4.00  inst_lit_activity_moves:                0
% 27.84/4.00  inst_num_tautologies:                   0
% 27.84/4.00  inst_num_prop_implied:                  0
% 27.84/4.00  inst_num_existing_simplified:           0
% 27.84/4.00  inst_num_eq_res_simplified:             0
% 27.84/4.00  inst_num_child_elim:                    0
% 27.84/4.00  inst_num_of_dismatching_blockings:      4545
% 27.84/4.00  inst_num_of_non_proper_insts:           7543
% 27.84/4.00  inst_num_of_duplicates:                 0
% 27.84/4.00  inst_inst_num_from_inst_to_res:         0
% 27.84/4.00  inst_dismatching_checking_time:         0.
% 27.84/4.00  
% 27.84/4.00  ------ Resolution
% 27.84/4.00  
% 27.84/4.00  res_num_of_clauses:                     163
% 27.84/4.00  res_num_in_passive:                     163
% 27.84/4.00  res_num_in_active:                      0
% 27.84/4.00  res_num_of_loops:                       601
% 27.84/4.00  res_forward_subset_subsumed:            315
% 27.84/4.00  res_backward_subset_subsumed:           120
% 27.84/4.00  res_forward_subsumed:                   0
% 27.84/4.00  res_backward_subsumed:                  0
% 27.84/4.00  res_forward_subsumption_resolution:     5
% 27.84/4.00  res_backward_subsumption_resolution:    0
% 27.84/4.00  res_clause_to_clause_subsumption:       11847
% 27.84/4.00  res_orphan_elimination:                 0
% 27.84/4.00  res_tautology_del:                      223
% 27.84/4.00  res_num_eq_res_simplified:              0
% 27.84/4.00  res_num_sel_changes:                    0
% 27.84/4.00  res_moves_from_active_to_pass:          0
% 27.84/4.00  
% 27.84/4.00  ------ Superposition
% 27.84/4.00  
% 27.84/4.00  sup_time_total:                         0.
% 27.84/4.00  sup_time_generating:                    0.
% 27.84/4.00  sup_time_sim_full:                      0.
% 27.84/4.00  sup_time_sim_immed:                     0.
% 27.84/4.00  
% 27.84/4.00  sup_num_of_clauses:                     2680
% 27.84/4.00  sup_num_in_active:                      383
% 27.84/4.00  sup_num_in_passive:                     2297
% 27.84/4.00  sup_num_of_loops:                       679
% 27.84/4.00  sup_fw_superposition:                   3286
% 27.84/4.00  sup_bw_superposition:                   3009
% 27.84/4.00  sup_immediate_simplified:               1501
% 27.84/4.00  sup_given_eliminated:                   2
% 27.84/4.00  comparisons_done:                       0
% 27.84/4.00  comparisons_avoided:                    97
% 27.84/4.00  
% 27.84/4.00  ------ Simplifications
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  sim_fw_subset_subsumed:                 554
% 27.84/4.00  sim_bw_subset_subsumed:                 614
% 27.84/4.00  sim_fw_subsumed:                        217
% 27.84/4.00  sim_bw_subsumed:                        32
% 27.84/4.00  sim_fw_subsumption_res:                 43
% 27.84/4.00  sim_bw_subsumption_res:                 1
% 27.84/4.00  sim_tautology_del:                      46
% 27.84/4.00  sim_eq_tautology_del:                   1513
% 27.84/4.00  sim_eq_res_simp:                        1
% 27.84/4.00  sim_fw_demodulated:                     410
% 27.84/4.00  sim_bw_demodulated:                     220
% 27.84/4.00  sim_light_normalised:                   399
% 27.84/4.00  sim_joinable_taut:                      0
% 27.84/4.00  sim_joinable_simp:                      0
% 27.84/4.00  sim_ac_normalised:                      0
% 27.84/4.00  sim_smt_subsumption:                    0
% 27.84/4.00  
%------------------------------------------------------------------------------
