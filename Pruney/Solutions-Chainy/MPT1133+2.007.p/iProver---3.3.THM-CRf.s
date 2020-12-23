%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:48 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  246 (9785 expanded)
%              Number of clauses        :  147 (2104 expanded)
%              Number of leaves         :   23 (2934 expanded)
%              Depth                    :   22
%              Number of atoms          : 1156 (116552 expanded)
%              Number of equality atoms :  415 (12171 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
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

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

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
    inference(ennf_transformation,[],[f26])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f70,plain,(
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
    inference(flattening,[],[f69])).

fof(f74,plain,(
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
     => ( ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK5 = X2
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
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
              | ~ v5_pre_topc(sK4,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK4,X0,X1) )
            & sK4 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
                  | ~ v5_pre_topc(X2,X0,sK3) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
                  | v5_pre_topc(X2,X0,sK3) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK2,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK2,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,
    ( ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ v5_pre_topc(sK4,sK2,sK3) )
    & ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK4,sK2,sK3) )
    & sK4 = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f70,f74,f73,f72,f71])).

fof(f125,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f75])).

fof(f129,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f75])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f43])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f126,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f75])).

fof(f124,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f75])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f128,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f75])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f38])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f59])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f132,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f81])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f133,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f80])).

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
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f23])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f54])).

fof(f115,plain,(
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
    inference(cnf_transformation,[],[f67])).

fof(f136,plain,(
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
    inference(equality_resolution,[],[f115])).

fof(f119,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f120,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f121,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f75])).

fof(f122,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f75])).

fof(f127,plain,(
    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f75])).

fof(f130,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

fof(f131,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f114,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f112,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f24,axiom,(
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
    inference(ennf_transformation,[],[f24])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f56])).

fof(f118,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f137,plain,(
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
    inference(equality_resolution,[],[f118])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f113,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,(
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
    inference(cnf_transformation,[],[f67])).

fof(f135,plain,(
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
    inference(equality_resolution,[],[f116])).

fof(f117,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f138,plain,(
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
    inference(equality_resolution,[],[f117])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f62])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_4350,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_45,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_4385,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4350,c_45])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4373,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7914,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4385,c_4373])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_63,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_50,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_4349,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_4384,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4349,c_45])).

cnf(c_8012,plain,
    ( v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7914,c_63,c_4384])).

cnf(c_27,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_4371,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8016,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v4_relat_1(sK5,u1_struct_0(sK2)) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8012,c_4371])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_65,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6635,plain,
    ( v5_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6636,plain,
    ( v5_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6635])).

cnf(c_10,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_15,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_645,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_15])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_655,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_645,c_12])).

cnf(c_4342,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_5595,plain,
    ( v5_relat_1(sK5,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4385,c_4342])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4374,plain,
    ( v1_funct_2(X0,X1,X2) = iProver_top
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7817,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top
    | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
    | v5_relat_1(sK5,X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5595,c_4374])).

cnf(c_6676,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),X0)
    | ~ v1_partfun1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_6677,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top
    | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6676])).

cnf(c_8145,plain,
    ( v5_relat_1(sK5,X0) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7817,c_63,c_5595,c_6677])).

cnf(c_8146,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top
    | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
    | v5_relat_1(sK5,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8145])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_5596,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_4342])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_4376,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7402,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_4376])).

cnf(c_7736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5596,c_7402])).

cnf(c_7737,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7736])).

cnf(c_4353,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_40,plain,
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
    inference(cnf_transformation,[],[f136])).

cnf(c_4358,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_7720,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4353,c_4358])).

cnf(c_55,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_56,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_54,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_57,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_53,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_58,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_52,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_59,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_64,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_44,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_4354,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_4386,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4354,c_45])).

cnf(c_43,negated_conjecture,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_4355,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_4387,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4355,c_45])).

cnf(c_38,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_4515,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_4516,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4515])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4599,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_4600,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4599])).

cnf(c_41,plain,
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
    inference(cnf_transformation,[],[f137])).

cnf(c_4615,plain,
    ( ~ v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,X0,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_4616,plain,
    ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,X0,sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4615])).

cnf(c_4618,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4616])).

cnf(c_37,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_4747,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_4748,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4747])).

cnf(c_39,plain,
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
    inference(cnf_transformation,[],[f135])).

cnf(c_4818,plain,
    ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_4824,plain,
    ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4818])).

cnf(c_4826,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4824])).

cnf(c_42,plain,
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
    inference(cnf_transformation,[],[f138])).

cnf(c_4831,plain,
    ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK5,X0,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_4832,plain,
    ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,X0,sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4831])).

cnf(c_4834,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4832])).

cnf(c_7937,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7720,c_56,c_57,c_58,c_59,c_63,c_64,c_65,c_4386,c_4384,c_4387,c_4385,c_4516,c_4600,c_4618,c_4748,c_4826,c_4834])).

cnf(c_7938,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7937])).

cnf(c_7941,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7938,c_56,c_57,c_58,c_59,c_63,c_64,c_65,c_4386,c_4384,c_4385,c_4516,c_4600,c_4748,c_4826,c_4834])).

cnf(c_7945,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7737,c_7941])).

cnf(c_7946,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v5_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5595,c_7941])).

cnf(c_8097,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7945,c_65,c_6636,c_7946])).

cnf(c_8151,plain,
    ( v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
    | v5_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8146,c_8097])).

cnf(c_8441,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8016,c_63,c_65,c_4384,c_6636,c_7914,c_8151])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4380,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X0
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_711,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_710])).

cnf(c_4341,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_5117,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4385,c_4341])).

cnf(c_6149,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4380,c_5117])).

cnf(c_8447,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8441,c_6149])).

cnf(c_4356,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_6525,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4353,c_4356])).

cnf(c_80,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_82,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_83,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_85,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_4500,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_4501,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4500])).

cnf(c_4614,plain,
    ( v5_pre_topc(sK5,X0,sK3)
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_4620,plain,
    ( v5_pre_topc(sK5,X0,sK3) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4614])).

cnf(c_4622,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4620])).

cnf(c_4797,plain,
    ( ~ v5_pre_topc(sK5,X0,sK3)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_4798,plain,
    ( v5_pre_topc(sK5,X0,sK3) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4797])).

cnf(c_4800,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4798])).

cnf(c_4815,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4615])).

cnf(c_4816,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4815])).

cnf(c_6936,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6525,c_56,c_57,c_58,c_59,c_63,c_64,c_65,c_82,c_85,c_4386,c_4384,c_4387,c_4385,c_4501,c_4622,c_4800,c_4816])).

cnf(c_6937,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6936])).

cnf(c_6940,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6937,c_56,c_57,c_58,c_59,c_63,c_64,c_65,c_82,c_85,c_4386,c_4384,c_4385,c_4501,c_4800,c_4816])).

cnf(c_7754,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7737,c_6940])).

cnf(c_5594,plain,
    ( v5_relat_1(sK5,X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4353,c_4342])).

cnf(c_6944,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v5_relat_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5594,c_6940])).

cnf(c_7228,plain,
    ( v5_relat_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_7229,plain,
    ( v5_relat_1(sK5,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7228])).

cnf(c_8092,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7754,c_4385,c_6944,c_7229])).

cnf(c_8588,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8447,c_8092])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4381,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8446,plain,
    ( u1_struct_0(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8441,c_4381])).

cnf(c_8631,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8588,c_8446])).

cnf(c_4352,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_8611,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8447,c_4352])).

cnf(c_7913,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4353,c_4373])).

cnf(c_7516,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_7517,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7516])).

cnf(c_8019,plain,
    ( v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7913,c_63,c_64,c_65,c_7517])).

cnf(c_8023,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8019,c_4371])).

cnf(c_7816,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_relat_1(sK5,X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5594,c_4374])).

cnf(c_8166,plain,
    ( v5_relat_1(sK5,X0) != iProver_top
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7816,c_63])).

cnf(c_8167,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top
    | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_relat_1(sK5,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8166])).

cnf(c_8172,plain,
    ( v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_relat_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8167,c_8092])).

cnf(c_8508,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8023,c_63,c_64,c_65,c_4385,c_7229,c_7517,c_8172])).

cnf(c_8512,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8508,c_8446])).

cnf(c_8515,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8512,c_4381])).

cnf(c_8619,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8611,c_8446,c_8515])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8631,c_8619])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:57:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.68/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.99  
% 3.68/0.99  ------  iProver source info
% 3.68/0.99  
% 3.68/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.99  git: non_committed_changes: false
% 3.68/0.99  git: last_make_outside_of_git: false
% 3.68/0.99  
% 3.68/0.99  ------ 
% 3.68/0.99  
% 3.68/0.99  ------ Input Options
% 3.68/0.99  
% 3.68/0.99  --out_options                           all
% 3.68/0.99  --tptp_safe_out                         true
% 3.68/0.99  --problem_path                          ""
% 3.68/0.99  --include_path                          ""
% 3.68/0.99  --clausifier                            res/vclausify_rel
% 3.68/0.99  --clausifier_options                    ""
% 3.68/0.99  --stdin                                 false
% 3.68/0.99  --stats_out                             all
% 3.68/0.99  
% 3.68/0.99  ------ General Options
% 3.68/0.99  
% 3.68/0.99  --fof                                   false
% 3.68/0.99  --time_out_real                         305.
% 3.68/0.99  --time_out_virtual                      -1.
% 3.68/0.99  --symbol_type_check                     false
% 3.68/0.99  --clausify_out                          false
% 3.68/0.99  --sig_cnt_out                           false
% 3.68/0.99  --trig_cnt_out                          false
% 3.68/0.99  --trig_cnt_out_tolerance                1.
% 3.68/0.99  --trig_cnt_out_sk_spl                   false
% 3.68/0.99  --abstr_cl_out                          false
% 3.68/0.99  
% 3.68/0.99  ------ Global Options
% 3.68/0.99  
% 3.68/0.99  --schedule                              default
% 3.68/0.99  --add_important_lit                     false
% 3.68/0.99  --prop_solver_per_cl                    1000
% 3.68/0.99  --min_unsat_core                        false
% 3.68/0.99  --soft_assumptions                      false
% 3.68/0.99  --soft_lemma_size                       3
% 3.68/0.99  --prop_impl_unit_size                   0
% 3.68/0.99  --prop_impl_unit                        []
% 3.68/0.99  --share_sel_clauses                     true
% 3.68/0.99  --reset_solvers                         false
% 3.68/0.99  --bc_imp_inh                            [conj_cone]
% 3.68/0.99  --conj_cone_tolerance                   3.
% 3.68/0.99  --extra_neg_conj                        none
% 3.68/0.99  --large_theory_mode                     true
% 3.68/0.99  --prolific_symb_bound                   200
% 3.68/0.99  --lt_threshold                          2000
% 3.68/0.99  --clause_weak_htbl                      true
% 3.68/0.99  --gc_record_bc_elim                     false
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing Options
% 3.68/0.99  
% 3.68/0.99  --preprocessing_flag                    true
% 3.68/0.99  --time_out_prep_mult                    0.1
% 3.68/0.99  --splitting_mode                        input
% 3.68/0.99  --splitting_grd                         true
% 3.68/0.99  --splitting_cvd                         false
% 3.68/0.99  --splitting_cvd_svl                     false
% 3.68/0.99  --splitting_nvd                         32
% 3.68/0.99  --sub_typing                            true
% 3.68/0.99  --prep_gs_sim                           true
% 3.68/0.99  --prep_unflatten                        true
% 3.68/0.99  --prep_res_sim                          true
% 3.68/0.99  --prep_upred                            true
% 3.68/0.99  --prep_sem_filter                       exhaustive
% 3.68/0.99  --prep_sem_filter_out                   false
% 3.68/0.99  --pred_elim                             true
% 3.68/0.99  --res_sim_input                         true
% 3.68/0.99  --eq_ax_congr_red                       true
% 3.68/0.99  --pure_diseq_elim                       true
% 3.68/0.99  --brand_transform                       false
% 3.68/0.99  --non_eq_to_eq                          false
% 3.68/0.99  --prep_def_merge                        true
% 3.68/0.99  --prep_def_merge_prop_impl              false
% 3.68/0.99  --prep_def_merge_mbd                    true
% 3.68/0.99  --prep_def_merge_tr_red                 false
% 3.68/0.99  --prep_def_merge_tr_cl                  false
% 3.68/0.99  --smt_preprocessing                     true
% 3.68/0.99  --smt_ac_axioms                         fast
% 3.68/0.99  --preprocessed_out                      false
% 3.68/0.99  --preprocessed_stats                    false
% 3.68/0.99  
% 3.68/0.99  ------ Abstraction refinement Options
% 3.68/0.99  
% 3.68/0.99  --abstr_ref                             []
% 3.68/0.99  --abstr_ref_prep                        false
% 3.68/0.99  --abstr_ref_until_sat                   false
% 3.68/0.99  --abstr_ref_sig_restrict                funpre
% 3.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.99  --abstr_ref_under                       []
% 3.68/0.99  
% 3.68/0.99  ------ SAT Options
% 3.68/0.99  
% 3.68/0.99  --sat_mode                              false
% 3.68/0.99  --sat_fm_restart_options                ""
% 3.68/0.99  --sat_gr_def                            false
% 3.68/0.99  --sat_epr_types                         true
% 3.68/0.99  --sat_non_cyclic_types                  false
% 3.68/0.99  --sat_finite_models                     false
% 3.68/0.99  --sat_fm_lemmas                         false
% 3.68/0.99  --sat_fm_prep                           false
% 3.68/0.99  --sat_fm_uc_incr                        true
% 3.68/0.99  --sat_out_model                         small
% 3.68/0.99  --sat_out_clauses                       false
% 3.68/0.99  
% 3.68/0.99  ------ QBF Options
% 3.68/0.99  
% 3.68/0.99  --qbf_mode                              false
% 3.68/0.99  --qbf_elim_univ                         false
% 3.68/0.99  --qbf_dom_inst                          none
% 3.68/0.99  --qbf_dom_pre_inst                      false
% 3.68/0.99  --qbf_sk_in                             false
% 3.68/0.99  --qbf_pred_elim                         true
% 3.68/0.99  --qbf_split                             512
% 3.68/0.99  
% 3.68/0.99  ------ BMC1 Options
% 3.68/0.99  
% 3.68/0.99  --bmc1_incremental                      false
% 3.68/0.99  --bmc1_axioms                           reachable_all
% 3.68/0.99  --bmc1_min_bound                        0
% 3.68/0.99  --bmc1_max_bound                        -1
% 3.68/0.99  --bmc1_max_bound_default                -1
% 3.68/0.99  --bmc1_symbol_reachability              true
% 3.68/0.99  --bmc1_property_lemmas                  false
% 3.68/0.99  --bmc1_k_induction                      false
% 3.68/0.99  --bmc1_non_equiv_states                 false
% 3.68/0.99  --bmc1_deadlock                         false
% 3.68/0.99  --bmc1_ucm                              false
% 3.68/0.99  --bmc1_add_unsat_core                   none
% 3.68/0.99  --bmc1_unsat_core_children              false
% 3.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.99  --bmc1_out_stat                         full
% 3.68/0.99  --bmc1_ground_init                      false
% 3.68/0.99  --bmc1_pre_inst_next_state              false
% 3.68/0.99  --bmc1_pre_inst_state                   false
% 3.68/0.99  --bmc1_pre_inst_reach_state             false
% 3.68/0.99  --bmc1_out_unsat_core                   false
% 3.68/0.99  --bmc1_aig_witness_out                  false
% 3.68/0.99  --bmc1_verbose                          false
% 3.68/0.99  --bmc1_dump_clauses_tptp                false
% 3.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.99  --bmc1_dump_file                        -
% 3.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.99  --bmc1_ucm_extend_mode                  1
% 3.68/0.99  --bmc1_ucm_init_mode                    2
% 3.68/0.99  --bmc1_ucm_cone_mode                    none
% 3.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.99  --bmc1_ucm_relax_model                  4
% 3.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.99  --bmc1_ucm_layered_model                none
% 3.68/0.99  --bmc1_ucm_max_lemma_size               10
% 3.68/0.99  
% 3.68/0.99  ------ AIG Options
% 3.68/0.99  
% 3.68/0.99  --aig_mode                              false
% 3.68/0.99  
% 3.68/0.99  ------ Instantiation Options
% 3.68/0.99  
% 3.68/0.99  --instantiation_flag                    true
% 3.68/0.99  --inst_sos_flag                         true
% 3.68/0.99  --inst_sos_phase                        true
% 3.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel_side                     num_symb
% 3.68/0.99  --inst_solver_per_active                1400
% 3.68/0.99  --inst_solver_calls_frac                1.
% 3.68/0.99  --inst_passive_queue_type               priority_queues
% 3.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.99  --inst_passive_queues_freq              [25;2]
% 3.68/0.99  --inst_dismatching                      true
% 3.68/0.99  --inst_eager_unprocessed_to_passive     true
% 3.68/0.99  --inst_prop_sim_given                   true
% 3.68/0.99  --inst_prop_sim_new                     false
% 3.68/0.99  --inst_subs_new                         false
% 3.68/0.99  --inst_eq_res_simp                      false
% 3.68/0.99  --inst_subs_given                       false
% 3.68/0.99  --inst_orphan_elimination               true
% 3.68/0.99  --inst_learning_loop_flag               true
% 3.68/0.99  --inst_learning_start                   3000
% 3.68/0.99  --inst_learning_factor                  2
% 3.68/0.99  --inst_start_prop_sim_after_learn       3
% 3.68/0.99  --inst_sel_renew                        solver
% 3.68/0.99  --inst_lit_activity_flag                true
% 3.68/0.99  --inst_restr_to_given                   false
% 3.68/0.99  --inst_activity_threshold               500
% 3.68/0.99  --inst_out_proof                        true
% 3.68/0.99  
% 3.68/0.99  ------ Resolution Options
% 3.68/0.99  
% 3.68/0.99  --resolution_flag                       true
% 3.68/0.99  --res_lit_sel                           adaptive
% 3.68/0.99  --res_lit_sel_side                      none
% 3.68/0.99  --res_ordering                          kbo
% 3.68/0.99  --res_to_prop_solver                    active
% 3.68/0.99  --res_prop_simpl_new                    false
% 3.68/0.99  --res_prop_simpl_given                  true
% 3.68/0.99  --res_passive_queue_type                priority_queues
% 3.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.99  --res_passive_queues_freq               [15;5]
% 3.68/0.99  --res_forward_subs                      full
% 3.68/0.99  --res_backward_subs                     full
% 3.68/0.99  --res_forward_subs_resolution           true
% 3.68/0.99  --res_backward_subs_resolution          true
% 3.68/0.99  --res_orphan_elimination                true
% 3.68/0.99  --res_time_limit                        2.
% 3.68/0.99  --res_out_proof                         true
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Options
% 3.68/0.99  
% 3.68/0.99  --superposition_flag                    true
% 3.68/0.99  --sup_passive_queue_type                priority_queues
% 3.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.99  --demod_completeness_check              fast
% 3.68/0.99  --demod_use_ground                      true
% 3.68/0.99  --sup_to_prop_solver                    passive
% 3.68/0.99  --sup_prop_simpl_new                    true
% 3.68/0.99  --sup_prop_simpl_given                  true
% 3.68/0.99  --sup_fun_splitting                     true
% 3.68/0.99  --sup_smt_interval                      50000
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Simplification Setup
% 3.68/0.99  
% 3.68/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_immed_triv                        [TrivRules]
% 3.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_bw_main                     []
% 3.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_input_bw                          []
% 3.68/0.99  
% 3.68/0.99  ------ Combination Options
% 3.68/0.99  
% 3.68/0.99  --comb_res_mult                         3
% 3.68/0.99  --comb_sup_mult                         2
% 3.68/0.99  --comb_inst_mult                        10
% 3.68/0.99  
% 3.68/0.99  ------ Debug Options
% 3.68/0.99  
% 3.68/0.99  --dbg_backtrace                         false
% 3.68/0.99  --dbg_dump_prop_clauses                 false
% 3.68/0.99  --dbg_dump_prop_clauses_file            -
% 3.68/0.99  --dbg_out_stat                          false
% 3.68/0.99  ------ Parsing...
% 3.68/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  ------ Proving...
% 3.68/0.99  ------ Problem Properties 
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  clauses                                 49
% 3.68/0.99  conjectures                             13
% 3.68/0.99  EPR                                     10
% 3.68/0.99  Horn                                    44
% 3.68/0.99  unary                                   23
% 3.68/0.99  binary                                  12
% 3.68/0.99  lits                                    127
% 3.68/0.99  lits eq                                 14
% 3.68/0.99  fd_pure                                 0
% 3.68/0.99  fd_pseudo                               0
% 3.68/0.99  fd_cond                                 6
% 3.68/0.99  fd_pseudo_cond                          1
% 3.68/0.99  AC symbols                              0
% 3.68/0.99  
% 3.68/0.99  ------ Schedule dynamic 5 is on 
% 3.68/0.99  
% 3.68/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ 
% 3.68/0.99  Current options:
% 3.68/0.99  ------ 
% 3.68/0.99  
% 3.68/0.99  ------ Input Options
% 3.68/0.99  
% 3.68/0.99  --out_options                           all
% 3.68/0.99  --tptp_safe_out                         true
% 3.68/0.99  --problem_path                          ""
% 3.68/0.99  --include_path                          ""
% 3.68/0.99  --clausifier                            res/vclausify_rel
% 3.68/0.99  --clausifier_options                    ""
% 3.68/0.99  --stdin                                 false
% 3.68/0.99  --stats_out                             all
% 3.68/0.99  
% 3.68/0.99  ------ General Options
% 3.68/0.99  
% 3.68/0.99  --fof                                   false
% 3.68/0.99  --time_out_real                         305.
% 3.68/0.99  --time_out_virtual                      -1.
% 3.68/0.99  --symbol_type_check                     false
% 3.68/0.99  --clausify_out                          false
% 3.68/0.99  --sig_cnt_out                           false
% 3.68/0.99  --trig_cnt_out                          false
% 3.68/0.99  --trig_cnt_out_tolerance                1.
% 3.68/0.99  --trig_cnt_out_sk_spl                   false
% 3.68/0.99  --abstr_cl_out                          false
% 3.68/0.99  
% 3.68/0.99  ------ Global Options
% 3.68/0.99  
% 3.68/0.99  --schedule                              default
% 3.68/0.99  --add_important_lit                     false
% 3.68/0.99  --prop_solver_per_cl                    1000
% 3.68/0.99  --min_unsat_core                        false
% 3.68/0.99  --soft_assumptions                      false
% 3.68/0.99  --soft_lemma_size                       3
% 3.68/0.99  --prop_impl_unit_size                   0
% 3.68/0.99  --prop_impl_unit                        []
% 3.68/0.99  --share_sel_clauses                     true
% 3.68/0.99  --reset_solvers                         false
% 3.68/0.99  --bc_imp_inh                            [conj_cone]
% 3.68/0.99  --conj_cone_tolerance                   3.
% 3.68/0.99  --extra_neg_conj                        none
% 3.68/0.99  --large_theory_mode                     true
% 3.68/0.99  --prolific_symb_bound                   200
% 3.68/0.99  --lt_threshold                          2000
% 3.68/0.99  --clause_weak_htbl                      true
% 3.68/0.99  --gc_record_bc_elim                     false
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing Options
% 3.68/0.99  
% 3.68/0.99  --preprocessing_flag                    true
% 3.68/0.99  --time_out_prep_mult                    0.1
% 3.68/0.99  --splitting_mode                        input
% 3.68/0.99  --splitting_grd                         true
% 3.68/0.99  --splitting_cvd                         false
% 3.68/0.99  --splitting_cvd_svl                     false
% 3.68/0.99  --splitting_nvd                         32
% 3.68/0.99  --sub_typing                            true
% 3.68/0.99  --prep_gs_sim                           true
% 3.68/0.99  --prep_unflatten                        true
% 3.68/0.99  --prep_res_sim                          true
% 3.68/0.99  --prep_upred                            true
% 3.68/0.99  --prep_sem_filter                       exhaustive
% 3.68/0.99  --prep_sem_filter_out                   false
% 3.68/0.99  --pred_elim                             true
% 3.68/0.99  --res_sim_input                         true
% 3.68/0.99  --eq_ax_congr_red                       true
% 3.68/0.99  --pure_diseq_elim                       true
% 3.68/0.99  --brand_transform                       false
% 3.68/0.99  --non_eq_to_eq                          false
% 3.68/0.99  --prep_def_merge                        true
% 3.68/0.99  --prep_def_merge_prop_impl              false
% 3.68/0.99  --prep_def_merge_mbd                    true
% 3.68/0.99  --prep_def_merge_tr_red                 false
% 3.68/0.99  --prep_def_merge_tr_cl                  false
% 3.68/0.99  --smt_preprocessing                     true
% 3.68/0.99  --smt_ac_axioms                         fast
% 3.68/0.99  --preprocessed_out                      false
% 3.68/0.99  --preprocessed_stats                    false
% 3.68/0.99  
% 3.68/0.99  ------ Abstraction refinement Options
% 3.68/0.99  
% 3.68/0.99  --abstr_ref                             []
% 3.68/0.99  --abstr_ref_prep                        false
% 3.68/0.99  --abstr_ref_until_sat                   false
% 3.68/0.99  --abstr_ref_sig_restrict                funpre
% 3.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.99  --abstr_ref_under                       []
% 3.68/0.99  
% 3.68/0.99  ------ SAT Options
% 3.68/0.99  
% 3.68/0.99  --sat_mode                              false
% 3.68/0.99  --sat_fm_restart_options                ""
% 3.68/0.99  --sat_gr_def                            false
% 3.68/0.99  --sat_epr_types                         true
% 3.68/0.99  --sat_non_cyclic_types                  false
% 3.68/0.99  --sat_finite_models                     false
% 3.68/0.99  --sat_fm_lemmas                         false
% 3.68/0.99  --sat_fm_prep                           false
% 3.68/0.99  --sat_fm_uc_incr                        true
% 3.68/0.99  --sat_out_model                         small
% 3.68/0.99  --sat_out_clauses                       false
% 3.68/0.99  
% 3.68/0.99  ------ QBF Options
% 3.68/0.99  
% 3.68/0.99  --qbf_mode                              false
% 3.68/0.99  --qbf_elim_univ                         false
% 3.68/0.99  --qbf_dom_inst                          none
% 3.68/0.99  --qbf_dom_pre_inst                      false
% 3.68/0.99  --qbf_sk_in                             false
% 3.68/0.99  --qbf_pred_elim                         true
% 3.68/0.99  --qbf_split                             512
% 3.68/0.99  
% 3.68/0.99  ------ BMC1 Options
% 3.68/0.99  
% 3.68/0.99  --bmc1_incremental                      false
% 3.68/0.99  --bmc1_axioms                           reachable_all
% 3.68/0.99  --bmc1_min_bound                        0
% 3.68/0.99  --bmc1_max_bound                        -1
% 3.68/0.99  --bmc1_max_bound_default                -1
% 3.68/0.99  --bmc1_symbol_reachability              true
% 3.68/0.99  --bmc1_property_lemmas                  false
% 3.68/0.99  --bmc1_k_induction                      false
% 3.68/0.99  --bmc1_non_equiv_states                 false
% 3.68/0.99  --bmc1_deadlock                         false
% 3.68/0.99  --bmc1_ucm                              false
% 3.68/0.99  --bmc1_add_unsat_core                   none
% 3.68/0.99  --bmc1_unsat_core_children              false
% 3.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.99  --bmc1_out_stat                         full
% 3.68/0.99  --bmc1_ground_init                      false
% 3.68/0.99  --bmc1_pre_inst_next_state              false
% 3.68/0.99  --bmc1_pre_inst_state                   false
% 3.68/0.99  --bmc1_pre_inst_reach_state             false
% 3.68/0.99  --bmc1_out_unsat_core                   false
% 3.68/0.99  --bmc1_aig_witness_out                  false
% 3.68/0.99  --bmc1_verbose                          false
% 3.68/0.99  --bmc1_dump_clauses_tptp                false
% 3.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.99  --bmc1_dump_file                        -
% 3.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.99  --bmc1_ucm_extend_mode                  1
% 3.68/0.99  --bmc1_ucm_init_mode                    2
% 3.68/0.99  --bmc1_ucm_cone_mode                    none
% 3.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.99  --bmc1_ucm_relax_model                  4
% 3.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.99  --bmc1_ucm_layered_model                none
% 3.68/0.99  --bmc1_ucm_max_lemma_size               10
% 3.68/0.99  
% 3.68/0.99  ------ AIG Options
% 3.68/0.99  
% 3.68/0.99  --aig_mode                              false
% 3.68/0.99  
% 3.68/0.99  ------ Instantiation Options
% 3.68/0.99  
% 3.68/0.99  --instantiation_flag                    true
% 3.68/0.99  --inst_sos_flag                         true
% 3.68/0.99  --inst_sos_phase                        true
% 3.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel_side                     none
% 3.68/0.99  --inst_solver_per_active                1400
% 3.68/0.99  --inst_solver_calls_frac                1.
% 3.68/0.99  --inst_passive_queue_type               priority_queues
% 3.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.99  --inst_passive_queues_freq              [25;2]
% 3.68/0.99  --inst_dismatching                      true
% 3.68/0.99  --inst_eager_unprocessed_to_passive     true
% 3.68/0.99  --inst_prop_sim_given                   true
% 3.68/0.99  --inst_prop_sim_new                     false
% 3.68/0.99  --inst_subs_new                         false
% 3.68/0.99  --inst_eq_res_simp                      false
% 3.68/0.99  --inst_subs_given                       false
% 3.68/0.99  --inst_orphan_elimination               true
% 3.68/0.99  --inst_learning_loop_flag               true
% 3.68/0.99  --inst_learning_start                   3000
% 3.68/0.99  --inst_learning_factor                  2
% 3.68/0.99  --inst_start_prop_sim_after_learn       3
% 3.68/0.99  --inst_sel_renew                        solver
% 3.68/0.99  --inst_lit_activity_flag                true
% 3.68/0.99  --inst_restr_to_given                   false
% 3.68/0.99  --inst_activity_threshold               500
% 3.68/0.99  --inst_out_proof                        true
% 3.68/0.99  
% 3.68/0.99  ------ Resolution Options
% 3.68/0.99  
% 3.68/0.99  --resolution_flag                       false
% 3.68/0.99  --res_lit_sel                           adaptive
% 3.68/0.99  --res_lit_sel_side                      none
% 3.68/0.99  --res_ordering                          kbo
% 3.68/0.99  --res_to_prop_solver                    active
% 3.68/0.99  --res_prop_simpl_new                    false
% 3.68/0.99  --res_prop_simpl_given                  true
% 3.68/0.99  --res_passive_queue_type                priority_queues
% 3.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.99  --res_passive_queues_freq               [15;5]
% 3.68/0.99  --res_forward_subs                      full
% 3.68/0.99  --res_backward_subs                     full
% 3.68/0.99  --res_forward_subs_resolution           true
% 3.68/0.99  --res_backward_subs_resolution          true
% 3.68/0.99  --res_orphan_elimination                true
% 3.68/0.99  --res_time_limit                        2.
% 3.68/0.99  --res_out_proof                         true
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Options
% 3.68/0.99  
% 3.68/0.99  --superposition_flag                    true
% 3.68/0.99  --sup_passive_queue_type                priority_queues
% 3.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.99  --demod_completeness_check              fast
% 3.68/0.99  --demod_use_ground                      true
% 3.68/0.99  --sup_to_prop_solver                    passive
% 3.68/0.99  --sup_prop_simpl_new                    true
% 3.68/0.99  --sup_prop_simpl_given                  true
% 3.68/0.99  --sup_fun_splitting                     true
% 3.68/0.99  --sup_smt_interval                      50000
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Simplification Setup
% 3.68/0.99  
% 3.68/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_immed_triv                        [TrivRules]
% 3.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_bw_main                     []
% 3.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_input_bw                          []
% 3.68/0.99  
% 3.68/0.99  ------ Combination Options
% 3.68/0.99  
% 3.68/0.99  --comb_res_mult                         3
% 3.68/0.99  --comb_sup_mult                         2
% 3.68/0.99  --comb_inst_mult                        10
% 3.68/0.99  
% 3.68/0.99  ------ Debug Options
% 3.68/0.99  
% 3.68/0.99  --dbg_backtrace                         false
% 3.68/0.99  --dbg_dump_prop_clauses                 false
% 3.68/0.99  --dbg_dump_prop_clauses_file            -
% 3.68/0.99  --dbg_out_stat                          false
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  % SZS status Theorem for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  fof(f25,conjecture,(
% 3.68/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f26,negated_conjecture,(
% 3.68/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.68/0.99    inference(negated_conjecture,[],[f25])).
% 3.68/0.99  
% 3.68/0.99  fof(f57,plain,(
% 3.68/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f26])).
% 3.68/0.99  
% 3.68/0.99  fof(f58,plain,(
% 3.68/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.68/0.99    inference(flattening,[],[f57])).
% 3.68/0.99  
% 3.68/0.99  fof(f69,plain,(
% 3.68/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.68/0.99    inference(nnf_transformation,[],[f58])).
% 3.68/0.99  
% 3.68/0.99  fof(f70,plain,(
% 3.68/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.68/0.99    inference(flattening,[],[f69])).
% 3.68/0.99  
% 3.68/0.99  fof(f74,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK5 = X2 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK5))) )),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f73,plain,(
% 3.68/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK4,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK4,X0,X1)) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f72,plain,(
% 3.68/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(X2,X0,sK3)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(X2,X0,sK3)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))) )),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f71,plain,(
% 3.68/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK2,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK2,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f75,plain,(
% 3.68/0.99    ((((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)) & sK4 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 3.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f70,f74,f73,f72,f71])).
% 3.68/0.99  
% 3.68/0.99  fof(f125,plain,(
% 3.68/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f129,plain,(
% 3.68/0.99    sK4 = sK5),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f15,axiom,(
% 3.68/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f43,plain,(
% 3.68/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.68/0.99    inference(ennf_transformation,[],[f15])).
% 3.68/0.99  
% 3.68/0.99  fof(f44,plain,(
% 3.68/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.68/0.99    inference(flattening,[],[f43])).
% 3.68/0.99  
% 3.68/0.99  fof(f98,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f44])).
% 3.68/0.99  
% 3.68/0.99  fof(f126,plain,(
% 3.68/0.99    v1_funct_1(sK5)),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f124,plain,(
% 3.68/0.99    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f17,axiom,(
% 3.68/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f47,plain,(
% 3.68/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.68/0.99    inference(ennf_transformation,[],[f17])).
% 3.68/0.99  
% 3.68/0.99  fof(f48,plain,(
% 3.68/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(flattening,[],[f47])).
% 3.68/0.99  
% 3.68/0.99  fof(f64,plain,(
% 3.68/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(nnf_transformation,[],[f48])).
% 3.68/0.99  
% 3.68/0.99  fof(f102,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f64])).
% 3.68/0.99  
% 3.68/0.99  fof(f128,plain,(
% 3.68/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f11,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f37,plain,(
% 3.68/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(ennf_transformation,[],[f11])).
% 3.68/0.99  
% 3.68/0.99  fof(f90,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f37])).
% 3.68/0.99  
% 3.68/0.99  fof(f8,axiom,(
% 3.68/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f34,plain,(
% 3.68/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(ennf_transformation,[],[f8])).
% 3.68/0.99  
% 3.68/0.99  fof(f61,plain,(
% 3.68/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(nnf_transformation,[],[f34])).
% 3.68/0.99  
% 3.68/0.99  fof(f85,plain,(
% 3.68/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f61])).
% 3.68/0.99  
% 3.68/0.99  fof(f12,axiom,(
% 3.68/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f38,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.68/0.99    inference(ennf_transformation,[],[f12])).
% 3.68/0.99  
% 3.68/0.99  fof(f39,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.68/0.99    inference(flattening,[],[f38])).
% 3.68/0.99  
% 3.68/0.99  fof(f91,plain,(
% 3.68/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f39])).
% 3.68/0.99  
% 3.68/0.99  fof(f10,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f36,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(ennf_transformation,[],[f10])).
% 3.68/0.99  
% 3.68/0.99  fof(f88,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f36])).
% 3.68/0.99  
% 3.68/0.99  fof(f14,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f41,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(ennf_transformation,[],[f14])).
% 3.68/0.99  
% 3.68/0.99  fof(f42,plain,(
% 3.68/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(flattening,[],[f41])).
% 3.68/0.99  
% 3.68/0.99  fof(f96,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f42])).
% 3.68/0.99  
% 3.68/0.99  fof(f4,axiom,(
% 3.68/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f59,plain,(
% 3.68/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.68/0.99    inference(nnf_transformation,[],[f4])).
% 3.68/0.99  
% 3.68/0.99  fof(f60,plain,(
% 3.68/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.68/0.99    inference(flattening,[],[f59])).
% 3.68/0.99  
% 3.68/0.99  fof(f81,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.68/0.99    inference(cnf_transformation,[],[f60])).
% 3.68/0.99  
% 3.68/0.99  fof(f132,plain,(
% 3.68/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.68/0.99    inference(equality_resolution,[],[f81])).
% 3.68/0.99  
% 3.68/0.99  fof(f80,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.68/0.99    inference(cnf_transformation,[],[f60])).
% 3.68/0.99  
% 3.68/0.99  fof(f133,plain,(
% 3.68/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.68/0.99    inference(equality_resolution,[],[f80])).
% 3.68/0.99  
% 3.68/0.99  fof(f23,axiom,(
% 3.68/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f53,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f23])).
% 3.68/0.99  
% 3.68/0.99  fof(f54,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/0.99    inference(flattening,[],[f53])).
% 3.68/0.99  
% 3.68/0.99  fof(f67,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/0.99    inference(nnf_transformation,[],[f54])).
% 3.68/0.99  
% 3.68/0.99  fof(f115,plain,(
% 3.68/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f67])).
% 3.68/0.99  
% 3.68/0.99  fof(f136,plain,(
% 3.68/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/0.99    inference(equality_resolution,[],[f115])).
% 3.68/0.99  
% 3.68/0.99  fof(f119,plain,(
% 3.68/0.99    v2_pre_topc(sK2)),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f120,plain,(
% 3.68/0.99    l1_pre_topc(sK2)),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f121,plain,(
% 3.68/0.99    v2_pre_topc(sK3)),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f122,plain,(
% 3.68/0.99    l1_pre_topc(sK3)),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f127,plain,(
% 3.68/0.99    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f130,plain,(
% 3.68/0.99    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f131,plain,(
% 3.68/0.99    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)),
% 3.68/0.99    inference(cnf_transformation,[],[f75])).
% 3.68/0.99  
% 3.68/0.99  fof(f22,axiom,(
% 3.68/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f27,plain,(
% 3.68/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.68/0.99    inference(pure_predicate_removal,[],[f22])).
% 3.68/0.99  
% 3.68/0.99  fof(f51,plain,(
% 3.68/0.99    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f27])).
% 3.68/0.99  
% 3.68/0.99  fof(f52,plain,(
% 3.68/0.99    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/0.99    inference(flattening,[],[f51])).
% 3.68/0.99  
% 3.68/0.99  fof(f114,plain,(
% 3.68/0.99    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f52])).
% 3.68/0.99  
% 3.68/0.99  fof(f20,axiom,(
% 3.68/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f28,plain,(
% 3.68/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.68/0.99    inference(pure_predicate_removal,[],[f20])).
% 3.68/0.99  
% 3.68/0.99  fof(f49,plain,(
% 3.68/0.99    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.68/0.99    inference(ennf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f112,plain,(
% 3.68/0.99    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f49])).
% 3.68/0.99  
% 3.68/0.99  fof(f24,axiom,(
% 3.68/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f55,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f24])).
% 3.68/0.99  
% 3.68/0.99  fof(f56,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/0.99    inference(flattening,[],[f55])).
% 3.68/0.99  
% 3.68/0.99  fof(f68,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/0.99    inference(nnf_transformation,[],[f56])).
% 3.68/0.99  
% 3.68/0.99  fof(f118,plain,(
% 3.68/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f68])).
% 3.68/0.99  
% 3.68/0.99  fof(f137,plain,(
% 3.68/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/0.99    inference(equality_resolution,[],[f118])).
% 3.68/0.99  
% 3.68/0.99  fof(f21,axiom,(
% 3.68/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f50,plain,(
% 3.68/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.68/0.99    inference(ennf_transformation,[],[f21])).
% 3.68/0.99  
% 3.68/0.99  fof(f113,plain,(
% 3.68/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f50])).
% 3.68/0.99  
% 3.68/0.99  fof(f116,plain,(
% 3.68/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f67])).
% 3.68/0.99  
% 3.68/0.99  fof(f135,plain,(
% 3.68/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/0.99    inference(equality_resolution,[],[f116])).
% 3.68/0.99  
% 3.68/0.99  fof(f117,plain,(
% 3.68/0.99    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f68])).
% 3.68/0.99  
% 3.68/0.99  fof(f138,plain,(
% 3.68/0.99    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/0.99    inference(equality_resolution,[],[f117])).
% 3.68/0.99  
% 3.68/0.99  fof(f3,axiom,(
% 3.68/0.99    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f30,plain,(
% 3.68/0.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.68/0.99    inference(ennf_transformation,[],[f3])).
% 3.68/0.99  
% 3.68/0.99  fof(f78,plain,(
% 3.68/0.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f30])).
% 3.68/0.99  
% 3.68/0.99  fof(f7,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f33,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.68/0.99    inference(ennf_transformation,[],[f7])).
% 3.68/0.99  
% 3.68/0.99  fof(f84,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f33])).
% 3.68/0.99  
% 3.68/0.99  fof(f13,axiom,(
% 3.68/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f40,plain,(
% 3.68/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.68/0.99    inference(ennf_transformation,[],[f13])).
% 3.68/0.99  
% 3.68/0.99  fof(f62,plain,(
% 3.68/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f63,plain,(
% 3.68/0.99    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f62])).
% 3.68/0.99  
% 3.68/0.99  fof(f92,plain,(
% 3.68/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.68/0.99    inference(cnf_transformation,[],[f63])).
% 3.68/0.99  
% 3.68/0.99  fof(f2,axiom,(
% 3.68/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f29,plain,(
% 3.68/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.68/0.99    inference(ennf_transformation,[],[f2])).
% 3.68/0.99  
% 3.68/0.99  fof(f77,plain,(
% 3.68/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f29])).
% 3.68/0.99  
% 3.68/0.99  cnf(c_49,negated_conjecture,
% 3.68/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f125]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4350,plain,
% 3.68/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_45,negated_conjecture,
% 3.68/0.99      ( sK4 = sK5 ),
% 3.68/0.99      inference(cnf_transformation,[],[f129]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4385,plain,
% 3.68/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_4350,c_45]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_21,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.99      | v1_partfun1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | v1_xboole_0(X2) ),
% 3.68/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4373,plain,
% 3.68/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.68/0.99      | v1_partfun1(X0,X1) = iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.68/0.99      | v1_funct_1(X0) != iProver_top
% 3.68/0.99      | v1_xboole_0(X2) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7914,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.68/0.99      | v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top
% 3.68/0.99      | v1_funct_1(sK5) != iProver_top
% 3.68/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_4385,c_4373]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_48,negated_conjecture,
% 3.68/0.99      ( v1_funct_1(sK5) ),
% 3.68/0.99      inference(cnf_transformation,[],[f126]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_63,plain,
% 3.68/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_50,negated_conjecture,
% 3.68/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f124]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4349,plain,
% 3.68/0.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4384,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_4349,c_45]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8012,plain,
% 3.68/0.99      ( v1_partfun1(sK5,u1_struct_0(sK2)) = iProver_top
% 3.68/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_7914,c_63,c_4384]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_27,plain,
% 3.68/0.99      ( ~ v1_partfun1(X0,X1)
% 3.68/0.99      | ~ v4_relat_1(X0,X1)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | k1_relat_1(X0) = X1 ),
% 3.68/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4371,plain,
% 3.68/0.99      ( k1_relat_1(X0) = X1
% 3.68/0.99      | v1_partfun1(X0,X1) != iProver_top
% 3.68/0.99      | v4_relat_1(X0,X1) != iProver_top
% 3.68/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8016,plain,
% 3.68/0.99      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.68/0.99      | v4_relat_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.68/0.99      | v1_relat_1(sK5) != iProver_top
% 3.68/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_8012,c_4371]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_46,negated_conjecture,
% 3.68/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f128]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_65,plain,
% 3.68/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_13,plain,
% 3.68/0.99      ( v5_relat_1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6635,plain,
% 3.68/0.99      ( v5_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.68/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6636,plain,
% 3.68/0.99      ( v5_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_6635]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_10,plain,
% 3.68/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 3.68/0.99      | ~ v5_relat_1(X0,X1)
% 3.68/0.99      | ~ v1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_15,plain,
% 3.68/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_645,plain,
% 3.68/0.99      ( ~ v5_relat_1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.68/0.99      | ~ v1_relat_1(X0) ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_10,c_15]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_12,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | v1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_655,plain,
% 3.68/0.99      ( ~ v5_relat_1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.68/0.99      inference(forward_subsumption_resolution,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_645,c_12]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4342,plain,
% 3.68/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5595,plain,
% 3.68/0.99      ( v5_relat_1(sK5,X0) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0))) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_4385,c_4342]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_19,plain,
% 3.68/0.99      ( v1_funct_2(X0,X1,X2)
% 3.68/0.99      | ~ v1_partfun1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ v1_funct_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4374,plain,
% 3.68/0.99      ( v1_funct_2(X0,X1,X2) = iProver_top
% 3.68/0.99      | v1_partfun1(X0,X1) != iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.68/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7817,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top
% 3.68/0.99      | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.68/0.99      | v5_relat_1(sK5,X0) != iProver_top
% 3.68/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_5595,c_4374]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6676,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),X0)
% 3.68/0.99      | ~ v1_partfun1(sK5,u1_struct_0(sK2))
% 3.68/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)))
% 3.68/0.99      | ~ v1_funct_1(sK5) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6677,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top
% 3.68/0.99      | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0))) != iProver_top
% 3.68/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_6676]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8145,plain,
% 3.68/0.99      ( v5_relat_1(sK5,X0) != iProver_top
% 3.68/0.99      | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_7817,c_63,c_5595,c_6677]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8146,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),X0) = iProver_top
% 3.68/0.99      | v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.68/0.99      | v5_relat_1(sK5,X0) != iProver_top ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_8145]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3,plain,
% 3.68/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.68/0.99      inference(cnf_transformation,[],[f132]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5596,plain,
% 3.68/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3,c_4342]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4,plain,
% 3.68/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.68/0.99      inference(cnf_transformation,[],[f133]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4376,plain,
% 3.68/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7402,plain,
% 3.68/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_4,c_4376]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7736,plain,
% 3.68/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_5596,c_7402]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7737,plain,
% 3.68/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_7736]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4353,plain,
% 3.68/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_40,plain,
% 3.68/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 3.68/0.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.68/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.68/0.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.68/0.99      | ~ v2_pre_topc(X1)
% 3.68/0.99      | ~ v2_pre_topc(X2)
% 3.68/0.99      | ~ l1_pre_topc(X1)
% 3.68/0.99      | ~ l1_pre_topc(X2)
% 3.68/0.99      | ~ v1_funct_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f136]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4358,plain,
% 3.68/0.99      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.68/0.99      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 3.68/0.99      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.68/0.99      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 3.68/0.99      | v2_pre_topc(X1) != iProver_top
% 3.68/0.99      | v2_pre_topc(X2) != iProver_top
% 3.68/0.99      | l1_pre_topc(X1) != iProver_top
% 3.68/0.99      | l1_pre_topc(X2) != iProver_top
% 3.68/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7720,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.68/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_4353,c_4358]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_55,negated_conjecture,
% 3.68/0.99      ( v2_pre_topc(sK2) ),
% 3.68/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_56,plain,
% 3.68/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_54,negated_conjecture,
% 3.68/0.99      ( l1_pre_topc(sK2) ),
% 3.68/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_57,plain,
% 3.68/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_53,negated_conjecture,
% 3.68/0.99      ( v2_pre_topc(sK3) ),
% 3.68/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_58,plain,
% 3.68/0.99      ( v2_pre_topc(sK3) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_52,negated_conjecture,
% 3.68/0.99      ( l1_pre_topc(sK3) ),
% 3.68/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_59,plain,
% 3.68/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_47,negated_conjecture,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f127]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_64,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_44,negated_conjecture,
% 3.68/0.99      ( v5_pre_topc(sK4,sK2,sK3)
% 3.68/0.99      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f130]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4354,plain,
% 3.68/0.99      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4386,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_4354,c_45]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_43,negated_conjecture,
% 3.68/0.99      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 3.68/0.99      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f131]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4355,plain,
% 3.68/0.99      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4387,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_4355,c_45]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_38,plain,
% 3.68/0.99      ( ~ v2_pre_topc(X0)
% 3.68/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.68/0.99      | ~ l1_pre_topc(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4515,plain,
% 3.68/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/0.99      | ~ v2_pre_topc(sK3)
% 3.68/0.99      | ~ l1_pre_topc(sK3) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_38]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4516,plain,
% 3.68/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.68/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_4515]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_36,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.68/0.99      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4599,plain,
% 3.68/0.99      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.68/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_36]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4600,plain,
% 3.68/0.99      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 3.68/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_4599]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_41,plain,
% 3.68/0.99      ( v5_pre_topc(X0,X1,X2)
% 3.68/0.99      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.68/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.68/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.68/0.99      | ~ v2_pre_topc(X1)
% 3.68/0.99      | ~ v2_pre_topc(X2)
% 3.68/0.99      | ~ l1_pre_topc(X1)
% 3.68/0.99      | ~ l1_pre_topc(X2)
% 3.68/0.99      | ~ v1_funct_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f137]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4615,plain,
% 3.68/0.99      ( ~ v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/0.99      | v5_pre_topc(sK5,X0,sK3)
% 3.68/0.99      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.68/0.99      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 3.68/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.68/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.68/0.99      | ~ v2_pre_topc(X0)
% 3.68/0.99      | ~ v2_pre_topc(sK3)
% 3.68/0.99      | ~ l1_pre_topc(X0)
% 3.68/0.99      | ~ l1_pre_topc(sK3)
% 3.68/0.99      | ~ v1_funct_1(sK5) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_41]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4616,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,X0,sK3) = iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 3.68/0.99      | v2_pre_topc(X0) != iProver_top
% 3.68/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.68/0.99      | l1_pre_topc(X0) != iProver_top
% 3.68/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.68/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_4615]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4618,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.68/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.68/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.68/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.68/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_4616]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_37,plain,
% 3.68/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.68/0.99      | ~ l1_pre_topc(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4747,plain,
% 3.68/0.99      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.68/0.99      | ~ l1_pre_topc(sK3) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_37]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4748,plain,
% 3.68/0.99      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 3.68/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_4747]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_39,plain,
% 3.68/0.99      ( v5_pre_topc(X0,X1,X2)
% 3.68/0.99      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.68/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.68/0.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.68/0.99      | ~ v2_pre_topc(X1)
% 3.68/0.99      | ~ v2_pre_topc(X2)
% 3.68/0.99      | ~ l1_pre_topc(X1)
% 3.68/0.99      | ~ l1_pre_topc(X2)
% 3.68/0.99      | ~ v1_funct_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f135]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4818,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/0.99      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/0.99      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.68/0.99      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.68/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.68/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.68/0.99      | ~ v2_pre_topc(X0)
% 3.68/0.99      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/0.99      | ~ l1_pre_topc(X0)
% 3.68/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/0.99      | ~ v1_funct_1(sK5) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_39]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4824,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/0.99      | v2_pre_topc(X0) != iProver_top
% 3.68/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | l1_pre_topc(X0) != iProver_top
% 3.68/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_4818]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4826,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.68/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_4824]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_42,plain,
% 3.68/0.99      ( ~ v5_pre_topc(X0,X1,X2)
% 3.68/0.99      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.68/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.68/0.99      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.68/0.99      | ~ v2_pre_topc(X1)
% 3.68/0.99      | ~ v2_pre_topc(X2)
% 3.68/0.99      | ~ l1_pre_topc(X1)
% 3.68/0.99      | ~ l1_pre_topc(X2)
% 3.68/0.99      | ~ v1_funct_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f138]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4831,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/0.99      | ~ v5_pre_topc(sK5,X0,sK3)
% 3.68/0.99      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.68/0.99      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 3.68/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.68/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.68/0.99      | ~ v2_pre_topc(X0)
% 3.68/0.99      | ~ v2_pre_topc(sK3)
% 3.68/0.99      | ~ l1_pre_topc(X0)
% 3.68/0.99      | ~ l1_pre_topc(sK3)
% 3.68/0.99      | ~ v1_funct_1(sK5) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_42]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4832,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,X0,sK3) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 3.68/0.99      | v2_pre_topc(X0) != iProver_top
% 3.68/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.68/0.99      | l1_pre_topc(X0) != iProver_top
% 3.68/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.68/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_4831]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4834,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.68/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.68/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.68/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.68/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_4832]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7937,plain,
% 3.68/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_7720,c_56,c_57,c_58,c_59,c_63,c_64,c_65,c_4386,c_4384,
% 3.68/0.99                 c_4387,c_4385,c_4516,c_4600,c_4618,c_4748,c_4826,c_4834]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7938,plain,
% 3.68/0.99      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_7937]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7941,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_7938,c_56,c_57,c_58,c_59,c_63,c_64,c_65,c_4386,c_4384,
% 3.68/0.99                 c_4385,c_4516,c_4600,c_4748,c_4826,c_4834]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7945,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_7737,c_7941]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7946,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/0.99      | v5_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_5595,c_7941]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8097,plain,
% 3.68/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_7945,c_65,c_6636,c_7946]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8151,plain,
% 3.68/0.99      ( v1_partfun1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.68/0.99      | v5_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_8146,c_8097]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8441,plain,
% 3.68/0.99      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_8016,c_63,c_65,c_4384,c_6636,c_7914,c_8151]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2,plain,
% 3.68/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4380,plain,
% 3.68/0.99      ( v1_xboole_0(X0) != iProver_top
% 3.68/0.99      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8,plain,
% 3.68/0.99      ( ~ r2_hidden(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.68/0.99      | ~ v1_xboole_0(X2) ),
% 3.68/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_18,plain,
% 3.68/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.68/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_710,plain,
% 3.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/1.00      | ~ v1_xboole_0(X1)
% 3.68/1.00      | X2 != X0
% 3.68/1.00      | sK0(X2) != X3
% 3.68/1.00      | k1_xboole_0 = X2 ),
% 3.68/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_711,plain,
% 3.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/1.00      | ~ v1_xboole_0(X1)
% 3.68/1.00      | k1_xboole_0 = X0 ),
% 3.68/1.00      inference(unflattening,[status(thm)],[c_710]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4341,plain,
% 3.68/1.00      ( k1_xboole_0 = X0
% 3.68/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.68/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_5117,plain,
% 3.68/1.00      ( sK5 = k1_xboole_0
% 3.68/1.00      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_4385,c_4341]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_6149,plain,
% 3.68/1.00      ( sK5 = k1_xboole_0
% 3.68/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_4380,c_5117]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8447,plain,
% 3.68/1.00      ( sK5 = k1_xboole_0 ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_8441,c_6149]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4356,plain,
% 3.68/1.00      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.68/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 3.68/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.68/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.68/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.68/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.68/1.00      | v2_pre_topc(X1) != iProver_top
% 3.68/1.00      | v2_pre_topc(X2) != iProver_top
% 3.68/1.00      | l1_pre_topc(X1) != iProver_top
% 3.68/1.00      | l1_pre_topc(X2) != iProver_top
% 3.68/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_6525,plain,
% 3.68/1.00      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.00      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.68/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.68/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_4353,c_4356]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_80,plain,
% 3.68/1.00      ( v2_pre_topc(X0) != iProver_top
% 3.68/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 3.68/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_82,plain,
% 3.68/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.68/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_80]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_83,plain,
% 3.68/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.68/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_85,plain,
% 3.68/1.00      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 3.68/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_83]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4500,plain,
% 3.68/1.00      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.68/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_36]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4501,plain,
% 3.68/1.00      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 3.68/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_4500]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4614,plain,
% 3.68/1.00      ( v5_pre_topc(sK5,X0,sK3)
% 3.68/1.00      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
% 3.68/1.00      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 3.68/1.00      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
% 3.68/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.68/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
% 3.68/1.00      | ~ v2_pre_topc(X0)
% 3.68/1.00      | ~ v2_pre_topc(sK3)
% 3.68/1.00      | ~ l1_pre_topc(X0)
% 3.68/1.00      | ~ l1_pre_topc(sK3)
% 3.68/1.00      | ~ v1_funct_1(sK5) ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_39]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4620,plain,
% 3.68/1.00      ( v5_pre_topc(sK5,X0,sK3) = iProver_top
% 3.68/1.00      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | v2_pre_topc(X0) != iProver_top
% 3.68/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.00      | l1_pre_topc(X0) != iProver_top
% 3.68/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_4614]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4622,plain,
% 3.68/1.00      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 3.68/1.00      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_4620]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4797,plain,
% 3.68/1.00      ( ~ v5_pre_topc(sK5,X0,sK3)
% 3.68/1.00      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
% 3.68/1.00      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 3.68/1.00      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
% 3.68/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.68/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
% 3.68/1.00      | ~ v2_pre_topc(X0)
% 3.68/1.00      | ~ v2_pre_topc(sK3)
% 3.68/1.00      | ~ l1_pre_topc(X0)
% 3.68/1.00      | ~ l1_pre_topc(sK3)
% 3.68/1.00      | ~ v1_funct_1(sK5) ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_40]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4798,plain,
% 3.68/1.00      ( v5_pre_topc(sK5,X0,sK3) != iProver_top
% 3.68/1.00      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3) = iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | v2_pre_topc(X0) != iProver_top
% 3.68/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.00      | l1_pre_topc(X0) != iProver_top
% 3.68/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_4797]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4800,plain,
% 3.68/1.00      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 3.68/1.00      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_4798]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4815,plain,
% 3.68/1.00      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/1.00      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.68/1.00      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.68/1.00      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 3.68/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.68/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 3.68/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.68/1.00      | ~ v2_pre_topc(sK3)
% 3.68/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.68/1.00      | ~ l1_pre_topc(sK3)
% 3.68/1.00      | ~ v1_funct_1(sK5) ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_4615]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4816,plain,
% 3.68/1.00      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.00      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.68/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.68/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_4815]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_6936,plain,
% 3.68/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_6525,c_56,c_57,c_58,c_59,c_63,c_64,c_65,c_82,c_85,
% 3.68/1.00                 c_4386,c_4384,c_4387,c_4385,c_4501,c_4622,c_4800,c_4816]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_6937,plain,
% 3.68/1.00      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 3.68/1.00      inference(renaming,[status(thm)],[c_6936]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_6940,plain,
% 3.68/1.00      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_6937,c_56,c_57,c_58,c_59,c_63,c_64,c_65,c_82,c_85,
% 3.68/1.00                 c_4386,c_4384,c_4385,c_4501,c_4800,c_4816]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_7754,plain,
% 3.68/1.00      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_7737,c_6940]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_5594,plain,
% 3.68/1.00      ( v5_relat_1(sK5,X0) != iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0))) = iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_4353,c_4342]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_6944,plain,
% 3.68/1.00      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.00      | v5_relat_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_5594,c_6940]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_7228,plain,
% 3.68/1.00      ( v5_relat_1(sK5,u1_struct_0(sK3))
% 3.68/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_7229,plain,
% 3.68/1.00      ( v5_relat_1(sK5,u1_struct_0(sK3)) = iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_7228]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8092,plain,
% 3.68/1.00      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_7754,c_4385,c_6944,c_7229]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8588,plain,
% 3.68/1.00      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 3.68/1.00      inference(demodulation,[status(thm)],[c_8447,c_8092]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_1,plain,
% 3.68/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.68/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4381,plain,
% 3.68/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8446,plain,
% 3.68/1.00      ( u1_struct_0(sK3) = k1_xboole_0 ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_8441,c_4381]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8631,plain,
% 3.68/1.00      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) != iProver_top ),
% 3.68/1.00      inference(light_normalisation,[status(thm)],[c_8588,c_8446]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_4352,plain,
% 3.68/1.00      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8611,plain,
% 3.68/1.00      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.00      inference(demodulation,[status(thm)],[c_8447,c_4352]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_7913,plain,
% 3.68/1.00      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.00      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
% 3.68/1.00      | v1_funct_1(sK5) != iProver_top
% 3.68/1.00      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_4353,c_4373]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_7516,plain,
% 3.68/1.00      ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.68/1.00      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
% 3.68/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.68/1.00      | ~ v1_funct_1(sK5)
% 3.68/1.00      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_7517,plain,
% 3.68/1.00      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.00      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
% 3.68/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/1.00      | v1_funct_1(sK5) != iProver_top
% 3.68/1.00      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_7516]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8019,plain,
% 3.68/1.00      ( v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
% 3.68/1.00      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_7913,c_63,c_64,c_65,c_7517]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8023,plain,
% 3.68/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 3.68/1.00      | v4_relat_1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 3.68/1.00      | v1_relat_1(sK5) != iProver_top
% 3.68/1.00      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_8019,c_4371]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_7816,plain,
% 3.68/1.00      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top
% 3.68/1.00      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 3.68/1.00      | v5_relat_1(sK5,X0) != iProver_top
% 3.68/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_5594,c_4374]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8166,plain,
% 3.68/1.00      ( v5_relat_1(sK5,X0) != iProver_top
% 3.68/1.00      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 3.68/1.00      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_7816,c_63]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8167,plain,
% 3.68/1.00      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),X0) = iProver_top
% 3.68/1.00      | v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 3.68/1.00      | v5_relat_1(sK5,X0) != iProver_top ),
% 3.68/1.00      inference(renaming,[status(thm)],[c_8166]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8172,plain,
% 3.68/1.00      ( v1_partfun1(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 3.68/1.00      | v5_relat_1(sK5,u1_struct_0(sK3)) != iProver_top ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_8167,c_8092]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8508,plain,
% 3.68/1.00      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.00      inference(global_propositional_subsumption,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_8023,c_63,c_64,c_65,c_4385,c_7229,c_7517,c_8172]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8512,plain,
% 3.68/1.00      ( v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.00      inference(light_normalisation,[status(thm)],[c_8508,c_8446]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8515,plain,
% 3.68/1.00      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3))) = k1_xboole_0 ),
% 3.68/1.00      inference(superposition,[status(thm)],[c_8512,c_4381]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_8619,plain,
% 3.68/1.00      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = iProver_top ),
% 3.68/1.00      inference(light_normalisation,[status(thm)],[c_8611,c_8446,c_8515]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(contradiction,plain,
% 3.68/1.00      ( $false ),
% 3.68/1.00      inference(minisat,[status(thm)],[c_8631,c_8619]) ).
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/1.00  
% 3.68/1.00  ------                               Statistics
% 3.68/1.00  
% 3.68/1.00  ------ General
% 3.68/1.00  
% 3.68/1.00  abstr_ref_over_cycles:                  0
% 3.68/1.00  abstr_ref_under_cycles:                 0
% 3.68/1.00  gc_basic_clause_elim:                   0
% 3.68/1.00  forced_gc_time:                         0
% 3.68/1.00  parsing_time:                           0.019
% 3.68/1.00  unif_index_cands_time:                  0.
% 3.68/1.00  unif_index_add_time:                    0.
% 3.68/1.00  orderings_time:                         0.
% 3.68/1.00  out_proof_time:                         0.019
% 3.68/1.00  total_time:                             0.291
% 3.68/1.00  num_of_symbols:                         60
% 3.68/1.00  num_of_terms:                           6262
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing
% 3.68/1.00  
% 3.68/1.00  num_of_splits:                          0
% 3.68/1.00  num_of_split_atoms:                     0
% 3.68/1.00  num_of_reused_defs:                     0
% 3.68/1.00  num_eq_ax_congr_red:                    26
% 3.68/1.00  num_of_sem_filtered_clauses:            1
% 3.68/1.00  num_of_subtypes:                        0
% 3.68/1.00  monotx_restored_types:                  0
% 3.68/1.00  sat_num_of_epr_types:                   0
% 3.68/1.00  sat_num_of_non_cyclic_types:            0
% 3.68/1.00  sat_guarded_non_collapsed_types:        0
% 3.68/1.00  num_pure_diseq_elim:                    0
% 3.68/1.00  simp_replaced_by:                       0
% 3.68/1.00  res_preprocessed:                       238
% 3.68/1.00  prep_upred:                             0
% 3.68/1.00  prep_unflattend:                        78
% 3.68/1.00  smt_new_axioms:                         0
% 3.68/1.00  pred_elim_cands:                        11
% 3.68/1.00  pred_elim:                              2
% 3.68/1.00  pred_elim_cl:                           3
% 3.68/1.00  pred_elim_cycles:                       12
% 3.68/1.00  merged_defs:                            8
% 3.68/1.00  merged_defs_ncl:                        0
% 3.68/1.00  bin_hyper_res:                          8
% 3.68/1.00  prep_cycles:                            4
% 3.68/1.00  pred_elim_time:                         0.05
% 3.68/1.00  splitting_time:                         0.
% 3.68/1.00  sem_filter_time:                        0.
% 3.68/1.00  monotx_time:                            0.
% 3.68/1.00  subtype_inf_time:                       0.
% 3.68/1.00  
% 3.68/1.00  ------ Problem properties
% 3.68/1.00  
% 3.68/1.00  clauses:                                49
% 3.68/1.00  conjectures:                            13
% 3.68/1.00  epr:                                    10
% 3.68/1.00  horn:                                   44
% 3.68/1.00  ground:                                 14
% 3.68/1.00  unary:                                  23
% 3.68/1.00  binary:                                 12
% 3.68/1.00  lits:                                   127
% 3.68/1.00  lits_eq:                                14
% 3.68/1.00  fd_pure:                                0
% 3.68/1.00  fd_pseudo:                              0
% 3.68/1.00  fd_cond:                                6
% 3.68/1.00  fd_pseudo_cond:                         1
% 3.68/1.00  ac_symbols:                             0
% 3.68/1.00  
% 3.68/1.00  ------ Propositional Solver
% 3.68/1.00  
% 3.68/1.00  prop_solver_calls:                      32
% 3.68/1.00  prop_fast_solver_calls:                 2258
% 3.68/1.00  smt_solver_calls:                       0
% 3.68/1.00  smt_fast_solver_calls:                  0
% 3.68/1.00  prop_num_of_clauses:                    2879
% 3.68/1.00  prop_preprocess_simplified:             9440
% 3.68/1.00  prop_fo_subsumed:                       73
% 3.68/1.00  prop_solver_time:                       0.
% 3.68/1.00  smt_solver_time:                        0.
% 3.68/1.00  smt_fast_solver_time:                   0.
% 3.68/1.00  prop_fast_solver_time:                  0.
% 3.68/1.00  prop_unsat_core_time:                   0.
% 3.68/1.00  
% 3.68/1.00  ------ QBF
% 3.68/1.00  
% 3.68/1.00  qbf_q_res:                              0
% 3.68/1.00  qbf_num_tautologies:                    0
% 3.68/1.00  qbf_prep_cycles:                        0
% 3.68/1.00  
% 3.68/1.00  ------ BMC1
% 3.68/1.00  
% 3.68/1.00  bmc1_current_bound:                     -1
% 3.68/1.00  bmc1_last_solved_bound:                 -1
% 3.68/1.00  bmc1_unsat_core_size:                   -1
% 3.68/1.00  bmc1_unsat_core_parents_size:           -1
% 3.68/1.00  bmc1_merge_next_fun:                    0
% 3.68/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.68/1.00  
% 3.68/1.00  ------ Instantiation
% 3.68/1.00  
% 3.68/1.00  inst_num_of_clauses:                    702
% 3.68/1.00  inst_num_in_passive:                    45
% 3.68/1.00  inst_num_in_active:                     464
% 3.68/1.00  inst_num_in_unprocessed:                194
% 3.68/1.00  inst_num_of_loops:                      530
% 3.68/1.00  inst_num_of_learning_restarts:          0
% 3.68/1.00  inst_num_moves_active_passive:          60
% 3.68/1.00  inst_lit_activity:                      0
% 3.68/1.00  inst_lit_activity_moves:                0
% 3.68/1.00  inst_num_tautologies:                   0
% 3.68/1.00  inst_num_prop_implied:                  0
% 3.68/1.00  inst_num_existing_simplified:           0
% 3.68/1.00  inst_num_eq_res_simplified:             0
% 3.68/1.00  inst_num_child_elim:                    0
% 3.68/1.00  inst_num_of_dismatching_blockings:      151
% 3.68/1.00  inst_num_of_non_proper_insts:           786
% 3.68/1.00  inst_num_of_duplicates:                 0
% 3.68/1.00  inst_inst_num_from_inst_to_res:         0
% 3.68/1.00  inst_dismatching_checking_time:         0.
% 3.68/1.00  
% 3.68/1.00  ------ Resolution
% 3.68/1.00  
% 3.68/1.00  res_num_of_clauses:                     0
% 3.68/1.00  res_num_in_passive:                     0
% 3.68/1.00  res_num_in_active:                      0
% 3.68/1.00  res_num_of_loops:                       242
% 3.68/1.00  res_forward_subset_subsumed:            68
% 3.68/1.00  res_backward_subset_subsumed:           2
% 3.68/1.00  res_forward_subsumed:                   0
% 3.68/1.00  res_backward_subsumed:                  0
% 3.68/1.00  res_forward_subsumption_resolution:     4
% 3.68/1.00  res_backward_subsumption_resolution:    0
% 3.68/1.00  res_clause_to_clause_subsumption:       492
% 3.68/1.00  res_orphan_elimination:                 0
% 3.68/1.00  res_tautology_del:                      83
% 3.68/1.00  res_num_eq_res_simplified:              0
% 3.68/1.00  res_num_sel_changes:                    0
% 3.68/1.00  res_moves_from_active_to_pass:          0
% 3.68/1.00  
% 3.68/1.00  ------ Superposition
% 3.68/1.00  
% 3.68/1.00  sup_time_total:                         0.
% 3.68/1.00  sup_time_generating:                    0.
% 3.68/1.00  sup_time_sim_full:                      0.
% 3.68/1.00  sup_time_sim_immed:                     0.
% 3.68/1.00  
% 3.68/1.00  sup_num_of_clauses:                     147
% 3.68/1.00  sup_num_in_active:                      49
% 3.68/1.00  sup_num_in_passive:                     98
% 3.68/1.00  sup_num_of_loops:                       104
% 3.68/1.00  sup_fw_superposition:                   139
% 3.68/1.00  sup_bw_superposition:                   65
% 3.68/1.00  sup_immediate_simplified:               55
% 3.68/1.00  sup_given_eliminated:                   3
% 3.68/1.00  comparisons_done:                       0
% 3.68/1.00  comparisons_avoided:                    0
% 3.68/1.00  
% 3.68/1.00  ------ Simplifications
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  sim_fw_subset_subsumed:                 16
% 3.68/1.00  sim_bw_subset_subsumed:                 25
% 3.68/1.00  sim_fw_subsumed:                        20
% 3.68/1.00  sim_bw_subsumed:                        6
% 3.68/1.00  sim_fw_subsumption_res:                 0
% 3.68/1.00  sim_bw_subsumption_res:                 0
% 3.68/1.00  sim_tautology_del:                      6
% 3.68/1.00  sim_eq_tautology_del:                   5
% 3.68/1.00  sim_eq_res_simp:                        0
% 3.68/1.00  sim_fw_demodulated:                     3
% 3.68/1.00  sim_bw_demodulated:                     37
% 3.68/1.00  sim_light_normalised:                   27
% 3.68/1.00  sim_joinable_taut:                      0
% 3.68/1.00  sim_joinable_simp:                      0
% 3.68/1.00  sim_ac_normalised:                      0
% 3.68/1.00  sim_smt_subsumption:                    0
% 3.68/1.00  
%------------------------------------------------------------------------------
