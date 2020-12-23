%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:53 EST 2020

% Result     : Theorem 23.65s
% Output     : CNFRefutation 23.65s
% Verified   : 
% Statistics : Number of formulae       :  442 (336570 expanded)
%              Number of clauses        :  320 (79036 expanded)
%              Number of leaves         :   30 (98032 expanded)
%              Depth                    :   51
%              Number of atoms          : 1773 (3827250 expanded)
%              Number of equality atoms :  827 (532546 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
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

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

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
    inference(nnf_transformation,[],[f55])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f75,plain,(
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

fof(f74,plain,(
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

fof(f73,plain,(
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

fof(f72,plain,
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

fof(f76,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f71,f75,f74,f73,f72])).

fof(f127,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f76])).

fof(f17,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f126,plain,(
    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f76])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f6,f64])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

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

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f117,plain,(
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
    inference(cnf_transformation,[],[f69])).

fof(f143,plain,(
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
    inference(equality_resolution,[],[f117])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f62])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f134,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f19,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f138,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f104])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f109,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f83,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f87])).

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

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f51])).

fof(f114,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f142,plain,(
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
    inference(equality_resolution,[],[f114])).

fof(f118,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f119,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f120,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f121,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f125,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

fof(f129,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f128,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f76])).

fof(f123,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f76])).

fof(f124,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f76])).

fof(f130,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f112,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f48,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f113,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f111,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f116,plain,(
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
    inference(cnf_transformation,[],[f69])).

fof(f144,plain,(
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
    inference(equality_resolution,[],[f116])).

fof(f115,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f141,plain,(
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
    inference(equality_resolution,[],[f115])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f57,f58])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f137,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f105])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f135,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f106])).

fof(f136,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f135])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f139,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f102])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2978,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2989,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8568,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_2989])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2995,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5729,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2978,c_2995])).

cnf(c_8586,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8568,c_5729])).

cnf(c_45,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_8614,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8586])).

cnf(c_12496,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8586,c_45,c_8614])).

cnf(c_12497,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_12496])).

cnf(c_12,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3002,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

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
    inference(cnf_transformation,[],[f143])).

cnf(c_2982,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6152,plain,
    ( v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),X0,X1) = iProver_top
    | v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v1_funct_2(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3002,c_2982])).

cnf(c_23564,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) = iProver_top
    | v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_funct_2(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(sK1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_1(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12497,c_6152])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f134])).

cnf(c_23859,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) = iProver_top
    | v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_funct_2(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(sK1(k1_xboole_0),k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_1(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23564,c_9])).

cnf(c_32,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_91,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_13,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_142,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_150,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_151,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_3474,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2988,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5728,plain,
    ( k1_relset_1(X0,X0,k6_partfun1(X0)) = k1_relat_1(k6_partfun1(X0)) ),
    inference(superposition,[status(thm)],[c_2988,c_2995])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_31,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_675,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_19,c_31])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_679,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_31,c_19,c_18])).

cnf(c_680,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_33,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 != X1
    | k6_partfun1(X3) != X0
    | k1_relat_1(X0) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_680,c_33])).

cnf(c_744,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_2967,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_4803,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2988,c_2967])).

cnf(c_5746,plain,
    ( k1_relset_1(X0,X0,k6_partfun1(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5728,c_4803])).

cnf(c_5763,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5746])).

cnf(c_1959,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_8551,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | X0 != k6_partfun1(k1_xboole_0)
    | X1 != k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_8553,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8551])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_9142,plain,
    ( ~ r1_tarski(X0,k6_partfun1(X1))
    | ~ r1_tarski(k6_partfun1(X1),X0)
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_9144,plain,
    ( ~ r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9142])).

cnf(c_12537,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12497,c_2978])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_12545,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12537,c_8])).

cnf(c_13169,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12545])).

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
    inference(cnf_transformation,[],[f142])).

cnf(c_2983,plain,
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

cnf(c_6760,plain,
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
    inference(superposition,[status(thm)],[c_2978,c_2983])).

cnf(c_53,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_54,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_52,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_55,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_56,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_50,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_57,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_61,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_62,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_63,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_42,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2979,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_43,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3135,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2979,c_43])).

cnf(c_48,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2974,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_3040,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2974,c_43])).

cnf(c_47,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2975,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_3045,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2975,c_43])).

cnf(c_41,negated_conjecture,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2980,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3140,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2980,c_43])).

cnf(c_35,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3388,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3389,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3388])).

cnf(c_36,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3412,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_3413,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3412])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3621,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_3622,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3621])).

cnf(c_3606,plain,
    ( v5_pre_topc(X0,sK2,X1)
    | ~ v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_4089,plain,
    ( ~ v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(X0,sK2,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_3606])).

cnf(c_4816,plain,
    ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4089])).

cnf(c_4817,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4816])).

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
    inference(cnf_transformation,[],[f144])).

cnf(c_3616,plain,
    ( ~ v5_pre_topc(X0,sK2,X1)
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_4129,plain,
    ( v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(X0,sK2,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_3616])).

cnf(c_4840,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4129])).

cnf(c_4841,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4840])).

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
    inference(cnf_transformation,[],[f141])).

cnf(c_3578,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)
    | v5_pre_topc(X0,sK2,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_4012,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_3578])).

cnf(c_5698,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4012])).

cnf(c_5699,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_5698])).

cnf(c_7101,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6760,c_54,c_55,c_56,c_57,c_61,c_62,c_63,c_3135,c_3040,c_3045,c_3140,c_3389,c_3413,c_3622,c_4817,c_4841,c_5699])).

cnf(c_7102,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7101])).

cnf(c_7105,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7102,c_54,c_55,c_56,c_57,c_61,c_62,c_63,c_3135,c_3040,c_3045,c_3389,c_3413,c_3622,c_4841,c_5699])).

cnf(c_12532,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12497,c_7105])).

cnf(c_12559,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12532,c_8])).

cnf(c_13170,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12559])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_17009,plain,
    ( r2_hidden(sK0(X0,k6_partfun1(X1)),X0)
    | r1_tarski(X0,k6_partfun1(X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_17016,plain,
    ( r2_hidden(sK0(k1_xboole_0,k6_partfun1(k1_xboole_0)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_17009])).

cnf(c_8569,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5) = u1_struct_0(sK2)
    | u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3045,c_2989])).

cnf(c_5730,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3045,c_2995])).

cnf(c_8579,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8569,c_5730])).

cnf(c_8737,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8579,c_3040])).

cnf(c_8738,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_8737])).

cnf(c_8772,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8738,c_3040])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_2993,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3159,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2993,c_8])).

cnf(c_9239,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8772,c_3159])).

cnf(c_8771,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8738,c_3045])).

cnf(c_8779,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8771,c_8])).

cnf(c_9547,plain,
    ( sK5 = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9239,c_8779])).

cnf(c_9548,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9547])).

cnf(c_2977,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_12538,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12497,c_2977])).

cnf(c_13212,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12538,c_3159])).

cnf(c_14033,plain,
    ( sK5 = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13212,c_12545])).

cnf(c_14034,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_14033])).

cnf(c_14038,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9548,c_14034])).

cnf(c_14075,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | sK5 = k1_xboole_0
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14034,c_2977])).

cnf(c_14074,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14034,c_2978])).

cnf(c_9576,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9548,c_7105])).

cnf(c_15908,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14074,c_9576])).

cnf(c_15931,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9548,c_15908])).

cnf(c_30275,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14038,c_14075,c_15931])).

cnf(c_30373,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_30275,c_12538])).

cnf(c_4395,plain,
    ( r2_hidden(sK0(X0,sK5),X0)
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4402,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
    | r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_4395])).

cnf(c_5539,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5541,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5539])).

cnf(c_3009,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2997,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7446,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_2997])).

cnf(c_12531,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12497,c_7446])).

cnf(c_12566,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12531,c_8])).

cnf(c_162,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13680,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12566,c_162])).

cnf(c_13681,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_13680])).

cnf(c_13688,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_13681])).

cnf(c_13689,plain,
    ( r1_tarski(sK5,X0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13688])).

cnf(c_13691,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_13689])).

cnf(c_24807,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X0,sK5),X0)
    | ~ v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_24809,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_24807])).

cnf(c_31920,plain,
    ( sK5 = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30373,c_142,c_3,c_4402,c_5541,c_13691,c_24809])).

cnf(c_31921,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_31920])).

cnf(c_6156,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_2982])).

cnf(c_3391,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3392,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3391])).

cnf(c_3415,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_3416,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3415])).

cnf(c_3629,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_3630,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3629])).

cnf(c_3588,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)
    | ~ v5_pre_topc(X0,sK2,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_4042,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ v5_pre_topc(X0,sK2,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_3588])).

cnf(c_4776,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | ~ v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4042])).

cnf(c_4777,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4776])).

cnf(c_2981,plain,
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

cnf(c_5378,plain,
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
    inference(superposition,[status(thm)],[c_2978,c_2981])).

cnf(c_4002,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | v5_pre_topc(X0,sK2,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_3578])).

cnf(c_4752,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4002])).

cnf(c_4753,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4752])).

cnf(c_5841,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5378,c_54,c_55,c_56,c_57,c_61,c_62,c_3040,c_3045,c_3140,c_3392,c_3416,c_3630,c_4753])).

cnf(c_5842,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5841])).

cnf(c_6683,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6156,c_54,c_55,c_56,c_57,c_61,c_62,c_3135,c_3040,c_3045,c_3392,c_3416,c_3630,c_4777,c_5842])).

cnf(c_6684,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6683])).

cnf(c_32019,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_31921,c_6684])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2998,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7516,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2978,c_2998])).

cnf(c_30378,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_30275,c_7516])).

cnf(c_30444,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | m1_subset_1(X0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30378,c_9])).

cnf(c_141,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_143,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(c_4401,plain,
    ( r2_hidden(sK0(X0,sK5),X0) = iProver_top
    | r1_tarski(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4395])).

cnf(c_4403,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4401])).

cnf(c_5540,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5539])).

cnf(c_5542,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5540])).

cnf(c_24808,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK0(X0,sK5),X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24807])).

cnf(c_24810,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24808])).

cnf(c_30379,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_30275,c_7446])).

cnf(c_30435,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30379,c_9])).

cnf(c_35422,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | sK5 = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30435,c_162])).

cnf(c_35423,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_35422])).

cnf(c_35431,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_35423])).

cnf(c_35433,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_35431])).

cnf(c_35545,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30444,c_143,c_162,c_4403,c_5542,c_24810,c_35433])).

cnf(c_35634,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_35545,c_7446])).

cnf(c_7447,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3045,c_2997])).

cnf(c_35636,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_35545,c_7447])).

cnf(c_35724,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35636,c_9])).

cnf(c_37770,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_35634,c_162,c_35724])).

cnf(c_37771,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_37770])).

cnf(c_37778,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_37771])).

cnf(c_37779,plain,
    ( r1_tarski(sK5,X0)
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_37778])).

cnf(c_37781,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | sK5 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_37779])).

cnf(c_37900,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32019,c_142,c_3,c_4402,c_5541,c_24809,c_37781])).

cnf(c_4800,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2988])).

cnf(c_7518,plain,
    ( m1_subset_1(X0,k1_xboole_0) = iProver_top
    | r2_hidden(X0,k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4800,c_2998])).

cnf(c_7448,plain,
    ( r2_hidden(X0,k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4800,c_2997])).

cnf(c_53925,plain,
    ( r2_hidden(X0,k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7518,c_162,c_7448])).

cnf(c_53932,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_53925])).

cnf(c_53933,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_53932])).

cnf(c_53935,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_53933])).

cnf(c_68428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X0,k6_partfun1(X2)),X0)
    | ~ v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_68430,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(sK0(k1_xboole_0,k6_partfun1(k1_xboole_0)),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_68428])).

cnf(c_24,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_2994,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3110,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2994,c_8])).

cnf(c_3001,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3114,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3110,c_3001])).

cnf(c_8769,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8738,c_2978])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_719,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_22,c_680])).

cnf(c_721,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_31,c_22,c_19,c_18])).

cnf(c_722,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_721])).

cnf(c_2968,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_9263,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8769,c_2968])).

cnf(c_15735,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12559,c_12545])).

cnf(c_15736,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15735])).

cnf(c_15742,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12497,c_15736])).

cnf(c_16288,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9263,c_8772,c_15742])).

cnf(c_16289,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_16288])).

cnf(c_8761,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8738,c_6684])).

cnf(c_8828,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8761,c_8])).

cnf(c_9475,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8828,c_8779])).

cnf(c_9476,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9475])).

cnf(c_16326,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16289,c_9476])).

cnf(c_20290,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,k1_relat_1(sK5),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8738,c_16326])).

cnf(c_37944,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_37900,c_20290])).

cnf(c_40120,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3114,c_37944])).

cnf(c_38025,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37900,c_2977])).

cnf(c_87473,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_40120,c_38025])).

cnf(c_8565,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3001,c_2989])).

cnf(c_5726,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3001,c_2995])).

cnf(c_8601,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8565,c_5726])).

cnf(c_89885,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_87473,c_8601])).

cnf(c_91464,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_89885,c_2981])).

cnf(c_92741,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_91464,c_8])).

cnf(c_5731,plain,
    ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2995])).

cnf(c_9455,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK5) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_8779,c_5731])).

cnf(c_2992,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3152,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2992,c_9])).

cnf(c_20775,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9455,c_3152])).

cnf(c_90,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_92,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_3476,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3474])).

cnf(c_18024,plain,
    ( ~ r1_tarski(X0,k6_partfun1(X1))
    | ~ r1_tarski(k6_partfun1(X1),X0)
    | k6_partfun1(X1) = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_18026,plain,
    ( ~ r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))
    | k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18024])).

cnf(c_60354,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v1_funct_2(sK5,X0,X1)
    | X1 != k1_xboole_0
    | X0 != k1_xboole_0
    | sK5 != k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8551])).

cnf(c_60359,plain,
    ( X0 != k1_xboole_0
    | X1 != k1_xboole_0
    | sK5 != k6_partfun1(k1_xboole_0)
    | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_2(sK5,X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60354])).

cnf(c_60361,plain,
    ( sK5 != k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60359])).

cnf(c_1951,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5545,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_60355,plain,
    ( k6_partfun1(k1_xboole_0) != X0
    | sK5 != X0
    | sK5 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5545])).

cnf(c_60365,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | sK5 = k6_partfun1(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_60355])).

cnf(c_96428,plain,
    ( v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20775,c_92,c_142,c_150,c_151,c_3,c_3476,c_4402,c_5541,c_5763,c_17016,c_18026,c_24809,c_37781,c_53935,c_60361,c_60365,c_68430])).

cnf(c_96432,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_96428,c_37900])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f139])).

cnf(c_2990,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3145,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2990,c_9])).

cnf(c_96437,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_96432,c_3145])).

cnf(c_96442,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_96437,c_5726])).

cnf(c_96447,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_92741,c_143,c_96442])).

cnf(c_5732,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2995])).

cnf(c_9454,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_8779,c_5732])).

cnf(c_27,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2991,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_20550,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9454,c_2991])).

cnf(c_20565,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20550,c_9])).

cnf(c_20551,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9454,c_3152])).

cnf(c_21678,plain,
    ( v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20565,c_8779,c_20551])).

cnf(c_21679,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | k1_relat_1(sK5) != k1_xboole_0
    | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_21678])).

cnf(c_37937,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_37900,c_21679])).

cnf(c_8622,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5726,c_3152])).

cnf(c_45007,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37937,c_143,c_8622])).

cnf(c_96724,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_96447,c_45007])).

cnf(c_96860,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_96724])).

cnf(c_37945,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_37900,c_16326])).

cnf(c_96735,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_96447,c_37945])).

cnf(c_96864,plain,
    ( u1_struct_0(sK2) = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_96860,c_96735])).

cnf(c_98654,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != X2
    | u1_struct_0(sK2) != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_98656,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != k1_xboole_0
    | u1_struct_0(sK2) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_98654])).

cnf(c_99312,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23859,c_91,c_142,c_150,c_151,c_3,c_3474,c_4402,c_5541,c_5763,c_8553,c_9144,c_12497,c_13169,c_13170,c_17016,c_24809,c_37781,c_53935,c_68430,c_96864,c_98656])).

cnf(c_99314,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_99312,c_37900,c_96447])).

cnf(c_38016,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_37900,c_6684])).

cnf(c_39627,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_38016,c_3001])).

cnf(c_99323,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_99314,c_39627])).

cnf(c_11889,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_11890,plain,
    ( u1_struct_0(sK2) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11889])).

cnf(c_1950,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6998,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1950])).

cnf(c_3563,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | X2 != u1_struct_0(sK3)
    | X1 != u1_struct_0(sK2)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_6997,plain,
    ( v1_funct_2(X0,X1,u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK2)
    | X0 != sK4
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3563])).

cnf(c_6999,plain,
    ( X0 != u1_struct_0(sK2)
    | X1 != sK4
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v1_funct_2(X1,X0,u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6997])).

cnf(c_7001,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | k1_xboole_0 != u1_struct_0(sK2)
    | k1_xboole_0 != sK4
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6999])).

cnf(c_3759,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_5552,plain,
    ( X0 = sK4
    | X0 != sK5
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_3759])).

cnf(c_5553,plain,
    ( sK4 != sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_5552])).

cnf(c_3713,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_3714,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3713])).

cnf(c_59,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99323,c_96864,c_37900,c_11890,c_6998,c_7001,c_5553,c_3714,c_151,c_150,c_43,c_59])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 23.65/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.65/3.49  
% 23.65/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.65/3.49  
% 23.65/3.49  ------  iProver source info
% 23.65/3.49  
% 23.65/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.65/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.65/3.49  git: non_committed_changes: false
% 23.65/3.49  git: last_make_outside_of_git: false
% 23.65/3.49  
% 23.65/3.49  ------ 
% 23.65/3.49  
% 23.65/3.49  ------ Input Options
% 23.65/3.49  
% 23.65/3.49  --out_options                           all
% 23.65/3.49  --tptp_safe_out                         true
% 23.65/3.49  --problem_path                          ""
% 23.65/3.49  --include_path                          ""
% 23.65/3.49  --clausifier                            res/vclausify_rel
% 23.65/3.49  --clausifier_options                    --mode clausify
% 23.65/3.49  --stdin                                 false
% 23.65/3.49  --stats_out                             all
% 23.65/3.49  
% 23.65/3.49  ------ General Options
% 23.65/3.49  
% 23.65/3.49  --fof                                   false
% 23.65/3.49  --time_out_real                         305.
% 23.65/3.49  --time_out_virtual                      -1.
% 23.65/3.49  --symbol_type_check                     false
% 23.65/3.49  --clausify_out                          false
% 23.65/3.49  --sig_cnt_out                           false
% 23.65/3.49  --trig_cnt_out                          false
% 23.65/3.49  --trig_cnt_out_tolerance                1.
% 23.65/3.49  --trig_cnt_out_sk_spl                   false
% 23.65/3.49  --abstr_cl_out                          false
% 23.65/3.49  
% 23.65/3.49  ------ Global Options
% 23.65/3.49  
% 23.65/3.49  --schedule                              default
% 23.65/3.49  --add_important_lit                     false
% 23.65/3.49  --prop_solver_per_cl                    1000
% 23.65/3.49  --min_unsat_core                        false
% 23.65/3.49  --soft_assumptions                      false
% 23.65/3.49  --soft_lemma_size                       3
% 23.65/3.49  --prop_impl_unit_size                   0
% 23.65/3.49  --prop_impl_unit                        []
% 23.65/3.49  --share_sel_clauses                     true
% 23.65/3.49  --reset_solvers                         false
% 23.65/3.49  --bc_imp_inh                            [conj_cone]
% 23.65/3.49  --conj_cone_tolerance                   3.
% 23.65/3.49  --extra_neg_conj                        none
% 23.65/3.49  --large_theory_mode                     true
% 23.65/3.49  --prolific_symb_bound                   200
% 23.65/3.49  --lt_threshold                          2000
% 23.65/3.49  --clause_weak_htbl                      true
% 23.65/3.49  --gc_record_bc_elim                     false
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing Options
% 23.65/3.49  
% 23.65/3.49  --preprocessing_flag                    true
% 23.65/3.49  --time_out_prep_mult                    0.1
% 23.65/3.49  --splitting_mode                        input
% 23.65/3.49  --splitting_grd                         true
% 23.65/3.49  --splitting_cvd                         false
% 23.65/3.49  --splitting_cvd_svl                     false
% 23.65/3.49  --splitting_nvd                         32
% 23.65/3.49  --sub_typing                            true
% 23.65/3.49  --prep_gs_sim                           true
% 23.65/3.49  --prep_unflatten                        true
% 23.65/3.49  --prep_res_sim                          true
% 23.65/3.49  --prep_upred                            true
% 23.65/3.49  --prep_sem_filter                       exhaustive
% 23.65/3.49  --prep_sem_filter_out                   false
% 23.65/3.49  --pred_elim                             true
% 23.65/3.49  --res_sim_input                         true
% 23.65/3.49  --eq_ax_congr_red                       true
% 23.65/3.49  --pure_diseq_elim                       true
% 23.65/3.49  --brand_transform                       false
% 23.65/3.49  --non_eq_to_eq                          false
% 23.65/3.49  --prep_def_merge                        true
% 23.65/3.49  --prep_def_merge_prop_impl              false
% 23.65/3.49  --prep_def_merge_mbd                    true
% 23.65/3.49  --prep_def_merge_tr_red                 false
% 23.65/3.49  --prep_def_merge_tr_cl                  false
% 23.65/3.49  --smt_preprocessing                     true
% 23.65/3.49  --smt_ac_axioms                         fast
% 23.65/3.49  --preprocessed_out                      false
% 23.65/3.49  --preprocessed_stats                    false
% 23.65/3.49  
% 23.65/3.49  ------ Abstraction refinement Options
% 23.65/3.49  
% 23.65/3.49  --abstr_ref                             []
% 23.65/3.49  --abstr_ref_prep                        false
% 23.65/3.49  --abstr_ref_until_sat                   false
% 23.65/3.49  --abstr_ref_sig_restrict                funpre
% 23.65/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.65/3.49  --abstr_ref_under                       []
% 23.65/3.49  
% 23.65/3.49  ------ SAT Options
% 23.65/3.49  
% 23.65/3.49  --sat_mode                              false
% 23.65/3.49  --sat_fm_restart_options                ""
% 23.65/3.49  --sat_gr_def                            false
% 23.65/3.49  --sat_epr_types                         true
% 23.65/3.49  --sat_non_cyclic_types                  false
% 23.65/3.49  --sat_finite_models                     false
% 23.65/3.49  --sat_fm_lemmas                         false
% 23.65/3.49  --sat_fm_prep                           false
% 23.65/3.49  --sat_fm_uc_incr                        true
% 23.65/3.49  --sat_out_model                         small
% 23.65/3.49  --sat_out_clauses                       false
% 23.65/3.49  
% 23.65/3.49  ------ QBF Options
% 23.65/3.49  
% 23.65/3.49  --qbf_mode                              false
% 23.65/3.49  --qbf_elim_univ                         false
% 23.65/3.49  --qbf_dom_inst                          none
% 23.65/3.49  --qbf_dom_pre_inst                      false
% 23.65/3.49  --qbf_sk_in                             false
% 23.65/3.49  --qbf_pred_elim                         true
% 23.65/3.49  --qbf_split                             512
% 23.65/3.49  
% 23.65/3.49  ------ BMC1 Options
% 23.65/3.49  
% 23.65/3.49  --bmc1_incremental                      false
% 23.65/3.49  --bmc1_axioms                           reachable_all
% 23.65/3.49  --bmc1_min_bound                        0
% 23.65/3.49  --bmc1_max_bound                        -1
% 23.65/3.49  --bmc1_max_bound_default                -1
% 23.65/3.49  --bmc1_symbol_reachability              true
% 23.65/3.49  --bmc1_property_lemmas                  false
% 23.65/3.49  --bmc1_k_induction                      false
% 23.65/3.49  --bmc1_non_equiv_states                 false
% 23.65/3.49  --bmc1_deadlock                         false
% 23.65/3.49  --bmc1_ucm                              false
% 23.65/3.49  --bmc1_add_unsat_core                   none
% 23.65/3.49  --bmc1_unsat_core_children              false
% 23.65/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.65/3.49  --bmc1_out_stat                         full
% 23.65/3.49  --bmc1_ground_init                      false
% 23.65/3.49  --bmc1_pre_inst_next_state              false
% 23.65/3.49  --bmc1_pre_inst_state                   false
% 23.65/3.49  --bmc1_pre_inst_reach_state             false
% 23.65/3.49  --bmc1_out_unsat_core                   false
% 23.65/3.49  --bmc1_aig_witness_out                  false
% 23.65/3.49  --bmc1_verbose                          false
% 23.65/3.49  --bmc1_dump_clauses_tptp                false
% 23.65/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.65/3.49  --bmc1_dump_file                        -
% 23.65/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.65/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.65/3.49  --bmc1_ucm_extend_mode                  1
% 23.65/3.49  --bmc1_ucm_init_mode                    2
% 23.65/3.49  --bmc1_ucm_cone_mode                    none
% 23.65/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.65/3.49  --bmc1_ucm_relax_model                  4
% 23.65/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.65/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.65/3.49  --bmc1_ucm_layered_model                none
% 23.65/3.49  --bmc1_ucm_max_lemma_size               10
% 23.65/3.49  
% 23.65/3.49  ------ AIG Options
% 23.65/3.49  
% 23.65/3.49  --aig_mode                              false
% 23.65/3.49  
% 23.65/3.49  ------ Instantiation Options
% 23.65/3.49  
% 23.65/3.49  --instantiation_flag                    true
% 23.65/3.49  --inst_sos_flag                         false
% 23.65/3.49  --inst_sos_phase                        true
% 23.65/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.65/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.65/3.49  --inst_lit_sel_side                     num_symb
% 23.65/3.49  --inst_solver_per_active                1400
% 23.65/3.49  --inst_solver_calls_frac                1.
% 23.65/3.49  --inst_passive_queue_type               priority_queues
% 23.65/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.65/3.49  --inst_passive_queues_freq              [25;2]
% 23.65/3.49  --inst_dismatching                      true
% 23.65/3.49  --inst_eager_unprocessed_to_passive     true
% 23.65/3.49  --inst_prop_sim_given                   true
% 23.65/3.49  --inst_prop_sim_new                     false
% 23.65/3.49  --inst_subs_new                         false
% 23.65/3.49  --inst_eq_res_simp                      false
% 23.65/3.49  --inst_subs_given                       false
% 23.65/3.49  --inst_orphan_elimination               true
% 23.65/3.49  --inst_learning_loop_flag               true
% 23.65/3.49  --inst_learning_start                   3000
% 23.65/3.49  --inst_learning_factor                  2
% 23.65/3.49  --inst_start_prop_sim_after_learn       3
% 23.65/3.49  --inst_sel_renew                        solver
% 23.65/3.49  --inst_lit_activity_flag                true
% 23.65/3.49  --inst_restr_to_given                   false
% 23.65/3.49  --inst_activity_threshold               500
% 23.65/3.49  --inst_out_proof                        true
% 23.65/3.49  
% 23.65/3.49  ------ Resolution Options
% 23.65/3.49  
% 23.65/3.49  --resolution_flag                       true
% 23.65/3.49  --res_lit_sel                           adaptive
% 23.65/3.49  --res_lit_sel_side                      none
% 23.65/3.49  --res_ordering                          kbo
% 23.65/3.49  --res_to_prop_solver                    active
% 23.65/3.49  --res_prop_simpl_new                    false
% 23.65/3.49  --res_prop_simpl_given                  true
% 23.65/3.49  --res_passive_queue_type                priority_queues
% 23.65/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.65/3.49  --res_passive_queues_freq               [15;5]
% 23.65/3.49  --res_forward_subs                      full
% 23.65/3.49  --res_backward_subs                     full
% 23.65/3.49  --res_forward_subs_resolution           true
% 23.65/3.49  --res_backward_subs_resolution          true
% 23.65/3.49  --res_orphan_elimination                true
% 23.65/3.49  --res_time_limit                        2.
% 23.65/3.49  --res_out_proof                         true
% 23.65/3.49  
% 23.65/3.49  ------ Superposition Options
% 23.65/3.49  
% 23.65/3.49  --superposition_flag                    true
% 23.65/3.49  --sup_passive_queue_type                priority_queues
% 23.65/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.65/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.65/3.49  --demod_completeness_check              fast
% 23.65/3.49  --demod_use_ground                      true
% 23.65/3.49  --sup_to_prop_solver                    passive
% 23.65/3.49  --sup_prop_simpl_new                    true
% 23.65/3.49  --sup_prop_simpl_given                  true
% 23.65/3.49  --sup_fun_splitting                     false
% 23.65/3.49  --sup_smt_interval                      50000
% 23.65/3.49  
% 23.65/3.49  ------ Superposition Simplification Setup
% 23.65/3.49  
% 23.65/3.49  --sup_indices_passive                   []
% 23.65/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.65/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_full_bw                           [BwDemod]
% 23.65/3.49  --sup_immed_triv                        [TrivRules]
% 23.65/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.65/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_immed_bw_main                     []
% 23.65/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.65/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.65/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.65/3.49  
% 23.65/3.49  ------ Combination Options
% 23.65/3.49  
% 23.65/3.49  --comb_res_mult                         3
% 23.65/3.49  --comb_sup_mult                         2
% 23.65/3.49  --comb_inst_mult                        10
% 23.65/3.49  
% 23.65/3.49  ------ Debug Options
% 23.65/3.49  
% 23.65/3.49  --dbg_backtrace                         false
% 23.65/3.49  --dbg_dump_prop_clauses                 false
% 23.65/3.49  --dbg_dump_prop_clauses_file            -
% 23.65/3.49  --dbg_out_stat                          false
% 23.65/3.49  ------ Parsing...
% 23.65/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.65/3.49  ------ Proving...
% 23.65/3.49  ------ Problem Properties 
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  clauses                                 48
% 23.65/3.49  conjectures                             13
% 23.65/3.49  EPR                                     11
% 23.65/3.49  Horn                                    40
% 23.65/3.49  unary                                   20
% 23.65/3.49  binary                                  9
% 23.65/3.49  lits                                    132
% 23.65/3.49  lits eq                                 19
% 23.65/3.49  fd_pure                                 0
% 23.65/3.49  fd_pseudo                               0
% 23.65/3.49  fd_cond                                 4
% 23.65/3.49  fd_pseudo_cond                          2
% 23.65/3.49  AC symbols                              0
% 23.65/3.49  
% 23.65/3.49  ------ Schedule dynamic 5 is on 
% 23.65/3.49  
% 23.65/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  ------ 
% 23.65/3.49  Current options:
% 23.65/3.49  ------ 
% 23.65/3.49  
% 23.65/3.49  ------ Input Options
% 23.65/3.49  
% 23.65/3.49  --out_options                           all
% 23.65/3.49  --tptp_safe_out                         true
% 23.65/3.49  --problem_path                          ""
% 23.65/3.49  --include_path                          ""
% 23.65/3.49  --clausifier                            res/vclausify_rel
% 23.65/3.49  --clausifier_options                    --mode clausify
% 23.65/3.49  --stdin                                 false
% 23.65/3.49  --stats_out                             all
% 23.65/3.49  
% 23.65/3.49  ------ General Options
% 23.65/3.49  
% 23.65/3.49  --fof                                   false
% 23.65/3.49  --time_out_real                         305.
% 23.65/3.49  --time_out_virtual                      -1.
% 23.65/3.49  --symbol_type_check                     false
% 23.65/3.49  --clausify_out                          false
% 23.65/3.49  --sig_cnt_out                           false
% 23.65/3.49  --trig_cnt_out                          false
% 23.65/3.49  --trig_cnt_out_tolerance                1.
% 23.65/3.49  --trig_cnt_out_sk_spl                   false
% 23.65/3.49  --abstr_cl_out                          false
% 23.65/3.49  
% 23.65/3.49  ------ Global Options
% 23.65/3.49  
% 23.65/3.49  --schedule                              default
% 23.65/3.49  --add_important_lit                     false
% 23.65/3.49  --prop_solver_per_cl                    1000
% 23.65/3.49  --min_unsat_core                        false
% 23.65/3.49  --soft_assumptions                      false
% 23.65/3.49  --soft_lemma_size                       3
% 23.65/3.49  --prop_impl_unit_size                   0
% 23.65/3.49  --prop_impl_unit                        []
% 23.65/3.49  --share_sel_clauses                     true
% 23.65/3.49  --reset_solvers                         false
% 23.65/3.49  --bc_imp_inh                            [conj_cone]
% 23.65/3.49  --conj_cone_tolerance                   3.
% 23.65/3.49  --extra_neg_conj                        none
% 23.65/3.49  --large_theory_mode                     true
% 23.65/3.49  --prolific_symb_bound                   200
% 23.65/3.49  --lt_threshold                          2000
% 23.65/3.49  --clause_weak_htbl                      true
% 23.65/3.49  --gc_record_bc_elim                     false
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing Options
% 23.65/3.49  
% 23.65/3.49  --preprocessing_flag                    true
% 23.65/3.49  --time_out_prep_mult                    0.1
% 23.65/3.49  --splitting_mode                        input
% 23.65/3.49  --splitting_grd                         true
% 23.65/3.49  --splitting_cvd                         false
% 23.65/3.49  --splitting_cvd_svl                     false
% 23.65/3.49  --splitting_nvd                         32
% 23.65/3.49  --sub_typing                            true
% 23.65/3.49  --prep_gs_sim                           true
% 23.65/3.49  --prep_unflatten                        true
% 23.65/3.49  --prep_res_sim                          true
% 23.65/3.49  --prep_upred                            true
% 23.65/3.49  --prep_sem_filter                       exhaustive
% 23.65/3.49  --prep_sem_filter_out                   false
% 23.65/3.49  --pred_elim                             true
% 23.65/3.49  --res_sim_input                         true
% 23.65/3.49  --eq_ax_congr_red                       true
% 23.65/3.49  --pure_diseq_elim                       true
% 23.65/3.49  --brand_transform                       false
% 23.65/3.49  --non_eq_to_eq                          false
% 23.65/3.49  --prep_def_merge                        true
% 23.65/3.49  --prep_def_merge_prop_impl              false
% 23.65/3.49  --prep_def_merge_mbd                    true
% 23.65/3.49  --prep_def_merge_tr_red                 false
% 23.65/3.49  --prep_def_merge_tr_cl                  false
% 23.65/3.49  --smt_preprocessing                     true
% 23.65/3.49  --smt_ac_axioms                         fast
% 23.65/3.49  --preprocessed_out                      false
% 23.65/3.49  --preprocessed_stats                    false
% 23.65/3.49  
% 23.65/3.49  ------ Abstraction refinement Options
% 23.65/3.49  
% 23.65/3.49  --abstr_ref                             []
% 23.65/3.49  --abstr_ref_prep                        false
% 23.65/3.49  --abstr_ref_until_sat                   false
% 23.65/3.49  --abstr_ref_sig_restrict                funpre
% 23.65/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.65/3.49  --abstr_ref_under                       []
% 23.65/3.49  
% 23.65/3.49  ------ SAT Options
% 23.65/3.49  
% 23.65/3.49  --sat_mode                              false
% 23.65/3.49  --sat_fm_restart_options                ""
% 23.65/3.49  --sat_gr_def                            false
% 23.65/3.49  --sat_epr_types                         true
% 23.65/3.49  --sat_non_cyclic_types                  false
% 23.65/3.49  --sat_finite_models                     false
% 23.65/3.49  --sat_fm_lemmas                         false
% 23.65/3.49  --sat_fm_prep                           false
% 23.65/3.49  --sat_fm_uc_incr                        true
% 23.65/3.49  --sat_out_model                         small
% 23.65/3.49  --sat_out_clauses                       false
% 23.65/3.49  
% 23.65/3.49  ------ QBF Options
% 23.65/3.49  
% 23.65/3.49  --qbf_mode                              false
% 23.65/3.49  --qbf_elim_univ                         false
% 23.65/3.49  --qbf_dom_inst                          none
% 23.65/3.49  --qbf_dom_pre_inst                      false
% 23.65/3.49  --qbf_sk_in                             false
% 23.65/3.49  --qbf_pred_elim                         true
% 23.65/3.49  --qbf_split                             512
% 23.65/3.49  
% 23.65/3.49  ------ BMC1 Options
% 23.65/3.49  
% 23.65/3.49  --bmc1_incremental                      false
% 23.65/3.49  --bmc1_axioms                           reachable_all
% 23.65/3.49  --bmc1_min_bound                        0
% 23.65/3.49  --bmc1_max_bound                        -1
% 23.65/3.49  --bmc1_max_bound_default                -1
% 23.65/3.49  --bmc1_symbol_reachability              true
% 23.65/3.49  --bmc1_property_lemmas                  false
% 23.65/3.49  --bmc1_k_induction                      false
% 23.65/3.49  --bmc1_non_equiv_states                 false
% 23.65/3.49  --bmc1_deadlock                         false
% 23.65/3.49  --bmc1_ucm                              false
% 23.65/3.49  --bmc1_add_unsat_core                   none
% 23.65/3.49  --bmc1_unsat_core_children              false
% 23.65/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.65/3.49  --bmc1_out_stat                         full
% 23.65/3.49  --bmc1_ground_init                      false
% 23.65/3.49  --bmc1_pre_inst_next_state              false
% 23.65/3.49  --bmc1_pre_inst_state                   false
% 23.65/3.49  --bmc1_pre_inst_reach_state             false
% 23.65/3.49  --bmc1_out_unsat_core                   false
% 23.65/3.49  --bmc1_aig_witness_out                  false
% 23.65/3.49  --bmc1_verbose                          false
% 23.65/3.49  --bmc1_dump_clauses_tptp                false
% 23.65/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.65/3.49  --bmc1_dump_file                        -
% 23.65/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.65/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.65/3.49  --bmc1_ucm_extend_mode                  1
% 23.65/3.49  --bmc1_ucm_init_mode                    2
% 23.65/3.49  --bmc1_ucm_cone_mode                    none
% 23.65/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.65/3.49  --bmc1_ucm_relax_model                  4
% 23.65/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.65/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.65/3.49  --bmc1_ucm_layered_model                none
% 23.65/3.49  --bmc1_ucm_max_lemma_size               10
% 23.65/3.49  
% 23.65/3.49  ------ AIG Options
% 23.65/3.49  
% 23.65/3.49  --aig_mode                              false
% 23.65/3.49  
% 23.65/3.49  ------ Instantiation Options
% 23.65/3.49  
% 23.65/3.49  --instantiation_flag                    true
% 23.65/3.49  --inst_sos_flag                         false
% 23.65/3.49  --inst_sos_phase                        true
% 23.65/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.65/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.65/3.49  --inst_lit_sel_side                     none
% 23.65/3.49  --inst_solver_per_active                1400
% 23.65/3.49  --inst_solver_calls_frac                1.
% 23.65/3.49  --inst_passive_queue_type               priority_queues
% 23.65/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.65/3.49  --inst_passive_queues_freq              [25;2]
% 23.65/3.49  --inst_dismatching                      true
% 23.65/3.49  --inst_eager_unprocessed_to_passive     true
% 23.65/3.49  --inst_prop_sim_given                   true
% 23.65/3.49  --inst_prop_sim_new                     false
% 23.65/3.49  --inst_subs_new                         false
% 23.65/3.49  --inst_eq_res_simp                      false
% 23.65/3.49  --inst_subs_given                       false
% 23.65/3.49  --inst_orphan_elimination               true
% 23.65/3.49  --inst_learning_loop_flag               true
% 23.65/3.49  --inst_learning_start                   3000
% 23.65/3.49  --inst_learning_factor                  2
% 23.65/3.49  --inst_start_prop_sim_after_learn       3
% 23.65/3.49  --inst_sel_renew                        solver
% 23.65/3.49  --inst_lit_activity_flag                true
% 23.65/3.49  --inst_restr_to_given                   false
% 23.65/3.49  --inst_activity_threshold               500
% 23.65/3.49  --inst_out_proof                        true
% 23.65/3.49  
% 23.65/3.49  ------ Resolution Options
% 23.65/3.49  
% 23.65/3.49  --resolution_flag                       false
% 23.65/3.49  --res_lit_sel                           adaptive
% 23.65/3.49  --res_lit_sel_side                      none
% 23.65/3.49  --res_ordering                          kbo
% 23.65/3.49  --res_to_prop_solver                    active
% 23.65/3.49  --res_prop_simpl_new                    false
% 23.65/3.49  --res_prop_simpl_given                  true
% 23.65/3.49  --res_passive_queue_type                priority_queues
% 23.65/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.65/3.49  --res_passive_queues_freq               [15;5]
% 23.65/3.49  --res_forward_subs                      full
% 23.65/3.49  --res_backward_subs                     full
% 23.65/3.49  --res_forward_subs_resolution           true
% 23.65/3.49  --res_backward_subs_resolution          true
% 23.65/3.49  --res_orphan_elimination                true
% 23.65/3.49  --res_time_limit                        2.
% 23.65/3.49  --res_out_proof                         true
% 23.65/3.49  
% 23.65/3.49  ------ Superposition Options
% 23.65/3.49  
% 23.65/3.49  --superposition_flag                    true
% 23.65/3.49  --sup_passive_queue_type                priority_queues
% 23.65/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.65/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.65/3.49  --demod_completeness_check              fast
% 23.65/3.49  --demod_use_ground                      true
% 23.65/3.49  --sup_to_prop_solver                    passive
% 23.65/3.49  --sup_prop_simpl_new                    true
% 23.65/3.49  --sup_prop_simpl_given                  true
% 23.65/3.49  --sup_fun_splitting                     false
% 23.65/3.49  --sup_smt_interval                      50000
% 23.65/3.49  
% 23.65/3.49  ------ Superposition Simplification Setup
% 23.65/3.49  
% 23.65/3.49  --sup_indices_passive                   []
% 23.65/3.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.65/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.65/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_full_bw                           [BwDemod]
% 23.65/3.49  --sup_immed_triv                        [TrivRules]
% 23.65/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.65/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_immed_bw_main                     []
% 23.65/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.65/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.65/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.65/3.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.65/3.49  
% 23.65/3.49  ------ Combination Options
% 23.65/3.49  
% 23.65/3.49  --comb_res_mult                         3
% 23.65/3.49  --comb_sup_mult                         2
% 23.65/3.49  --comb_inst_mult                        10
% 23.65/3.49  
% 23.65/3.49  ------ Debug Options
% 23.65/3.49  
% 23.65/3.49  --dbg_backtrace                         false
% 23.65/3.49  --dbg_dump_prop_clauses                 false
% 23.65/3.49  --dbg_dump_prop_clauses_file            -
% 23.65/3.49  --dbg_out_stat                          false
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  ------ Proving...
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  % SZS status Theorem for theBenchmark.p
% 23.65/3.49  
% 23.65/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.65/3.49  
% 23.65/3.49  fof(f25,conjecture,(
% 23.65/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f26,negated_conjecture,(
% 23.65/3.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 23.65/3.49    inference(negated_conjecture,[],[f25])).
% 23.65/3.49  
% 23.65/3.49  fof(f54,plain,(
% 23.65/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 23.65/3.49    inference(ennf_transformation,[],[f26])).
% 23.65/3.49  
% 23.65/3.49  fof(f55,plain,(
% 23.65/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.65/3.49    inference(flattening,[],[f54])).
% 23.65/3.49  
% 23.65/3.49  fof(f70,plain,(
% 23.65/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.65/3.49    inference(nnf_transformation,[],[f55])).
% 23.65/3.49  
% 23.65/3.49  fof(f71,plain,(
% 23.65/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.65/3.49    inference(flattening,[],[f70])).
% 23.65/3.49  
% 23.65/3.49  fof(f75,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK5 = X2 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK5))) )),
% 23.65/3.49    introduced(choice_axiom,[])).
% 23.65/3.49  
% 23.65/3.49  fof(f74,plain,(
% 23.65/3.49    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK4,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK4,X0,X1)) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 23.65/3.49    introduced(choice_axiom,[])).
% 23.65/3.49  
% 23.65/3.49  fof(f73,plain,(
% 23.65/3.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(X2,X0,sK3)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(X2,X0,sK3)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))) )),
% 23.65/3.49    introduced(choice_axiom,[])).
% 23.65/3.49  
% 23.65/3.49  fof(f72,plain,(
% 23.65/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK2,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK2,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 23.65/3.49    introduced(choice_axiom,[])).
% 23.65/3.49  
% 23.65/3.49  fof(f76,plain,(
% 23.65/3.49    ((((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)) & sK4 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 23.65/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f71,f75,f74,f73,f72])).
% 23.65/3.49  
% 23.65/3.49  fof(f127,plain,(
% 23.65/3.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f17,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f42,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.65/3.49    inference(ennf_transformation,[],[f17])).
% 23.65/3.49  
% 23.65/3.49  fof(f43,plain,(
% 23.65/3.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.65/3.49    inference(flattening,[],[f42])).
% 23.65/3.49  
% 23.65/3.49  fof(f66,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.65/3.49    inference(nnf_transformation,[],[f43])).
% 23.65/3.49  
% 23.65/3.49  fof(f101,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f66])).
% 23.65/3.49  
% 23.65/3.49  fof(f15,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f39,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.65/3.49    inference(ennf_transformation,[],[f15])).
% 23.65/3.49  
% 23.65/3.49  fof(f98,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f39])).
% 23.65/3.49  
% 23.65/3.49  fof(f126,plain,(
% 23.65/3.49    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f6,axiom,(
% 23.65/3.49    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f64,plain,(
% 23.65/3.49    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 23.65/3.49    introduced(choice_axiom,[])).
% 23.65/3.49  
% 23.65/3.49  fof(f65,plain,(
% 23.65/3.49    ! [X0] : (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 23.65/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f6,f64])).
% 23.65/3.49  
% 23.65/3.49  fof(f88,plain,(
% 23.65/3.49    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f65])).
% 23.65/3.49  
% 23.65/3.49  fof(f24,axiom,(
% 23.65/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f52,plain,(
% 23.65/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.65/3.49    inference(ennf_transformation,[],[f24])).
% 23.65/3.49  
% 23.65/3.49  fof(f53,plain,(
% 23.65/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.65/3.49    inference(flattening,[],[f52])).
% 23.65/3.49  
% 23.65/3.49  fof(f69,plain,(
% 23.65/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.65/3.49    inference(nnf_transformation,[],[f53])).
% 23.65/3.49  
% 23.65/3.49  fof(f117,plain,(
% 23.65/3.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f69])).
% 23.65/3.49  
% 23.65/3.49  fof(f143,plain,(
% 23.65/3.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.65/3.49    inference(equality_resolution,[],[f117])).
% 23.65/3.49  
% 23.65/3.49  fof(f5,axiom,(
% 23.65/3.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f62,plain,(
% 23.65/3.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 23.65/3.49    inference(nnf_transformation,[],[f5])).
% 23.65/3.49  
% 23.65/3.49  fof(f63,plain,(
% 23.65/3.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 23.65/3.49    inference(flattening,[],[f62])).
% 23.65/3.49  
% 23.65/3.49  fof(f86,plain,(
% 23.65/3.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 23.65/3.49    inference(cnf_transformation,[],[f63])).
% 23.65/3.49  
% 23.65/3.49  fof(f134,plain,(
% 23.65/3.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 23.65/3.49    inference(equality_resolution,[],[f86])).
% 23.65/3.49  
% 23.65/3.49  fof(f19,axiom,(
% 23.65/3.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f110,plain,(
% 23.65/3.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f19])).
% 23.65/3.49  
% 23.65/3.49  fof(f7,axiom,(
% 23.65/3.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f90,plain,(
% 23.65/3.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f7])).
% 23.65/3.49  
% 23.65/3.49  fof(f85,plain,(
% 23.65/3.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f63])).
% 23.65/3.49  
% 23.65/3.49  fof(f2,axiom,(
% 23.65/3.49    v1_xboole_0(k1_xboole_0)),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f80,plain,(
% 23.65/3.49    v1_xboole_0(k1_xboole_0)),
% 23.65/3.49    inference(cnf_transformation,[],[f2])).
% 23.65/3.49  
% 23.65/3.49  fof(f104,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f66])).
% 23.65/3.49  
% 23.65/3.49  fof(f138,plain,(
% 23.65/3.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 23.65/3.49    inference(equality_resolution,[],[f104])).
% 23.65/3.49  
% 23.65/3.49  fof(f13,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f29,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 23.65/3.49    inference(pure_predicate_removal,[],[f13])).
% 23.65/3.49  
% 23.65/3.49  fof(f37,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.65/3.49    inference(ennf_transformation,[],[f29])).
% 23.65/3.49  
% 23.65/3.49  fof(f96,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f37])).
% 23.65/3.49  
% 23.65/3.49  fof(f18,axiom,(
% 23.65/3.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f44,plain,(
% 23.65/3.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 23.65/3.49    inference(ennf_transformation,[],[f18])).
% 23.65/3.49  
% 23.65/3.49  fof(f45,plain,(
% 23.65/3.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.65/3.49    inference(flattening,[],[f44])).
% 23.65/3.49  
% 23.65/3.49  fof(f67,plain,(
% 23.65/3.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.65/3.49    inference(nnf_transformation,[],[f45])).
% 23.65/3.49  
% 23.65/3.49  fof(f107,plain,(
% 23.65/3.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f67])).
% 23.65/3.49  
% 23.65/3.49  fof(f12,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f36,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.65/3.49    inference(ennf_transformation,[],[f12])).
% 23.65/3.49  
% 23.65/3.49  fof(f95,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f36])).
% 23.65/3.49  
% 23.65/3.49  fof(f109,plain,(
% 23.65/3.49    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f19])).
% 23.65/3.49  
% 23.65/3.49  fof(f3,axiom,(
% 23.65/3.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f60,plain,(
% 23.65/3.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.65/3.49    inference(nnf_transformation,[],[f3])).
% 23.65/3.49  
% 23.65/3.49  fof(f61,plain,(
% 23.65/3.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.65/3.49    inference(flattening,[],[f60])).
% 23.65/3.49  
% 23.65/3.49  fof(f83,plain,(
% 23.65/3.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f61])).
% 23.65/3.49  
% 23.65/3.49  fof(f87,plain,(
% 23.65/3.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 23.65/3.49    inference(cnf_transformation,[],[f63])).
% 23.65/3.49  
% 23.65/3.49  fof(f133,plain,(
% 23.65/3.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 23.65/3.49    inference(equality_resolution,[],[f87])).
% 23.65/3.49  
% 23.65/3.49  fof(f23,axiom,(
% 23.65/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f50,plain,(
% 23.65/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.65/3.49    inference(ennf_transformation,[],[f23])).
% 23.65/3.49  
% 23.65/3.49  fof(f51,plain,(
% 23.65/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.65/3.49    inference(flattening,[],[f50])).
% 23.65/3.49  
% 23.65/3.49  fof(f68,plain,(
% 23.65/3.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.65/3.49    inference(nnf_transformation,[],[f51])).
% 23.65/3.49  
% 23.65/3.49  fof(f114,plain,(
% 23.65/3.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f68])).
% 23.65/3.49  
% 23.65/3.49  fof(f142,plain,(
% 23.65/3.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.65/3.49    inference(equality_resolution,[],[f114])).
% 23.65/3.49  
% 23.65/3.49  fof(f118,plain,(
% 23.65/3.49    v2_pre_topc(sK2)),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f119,plain,(
% 23.65/3.49    l1_pre_topc(sK2)),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f120,plain,(
% 23.65/3.49    v2_pre_topc(sK3)),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f121,plain,(
% 23.65/3.49    l1_pre_topc(sK3)),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f125,plain,(
% 23.65/3.49    v1_funct_1(sK5)),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f129,plain,(
% 23.65/3.49    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f128,plain,(
% 23.65/3.49    sK4 = sK5),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f123,plain,(
% 23.65/3.49    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f124,plain,(
% 23.65/3.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f130,plain,(
% 23.65/3.49    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)),
% 23.65/3.49    inference(cnf_transformation,[],[f76])).
% 23.65/3.49  
% 23.65/3.49  fof(f21,axiom,(
% 23.65/3.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f47,plain,(
% 23.65/3.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.65/3.49    inference(ennf_transformation,[],[f21])).
% 23.65/3.49  
% 23.65/3.49  fof(f112,plain,(
% 23.65/3.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f47])).
% 23.65/3.49  
% 23.65/3.49  fof(f22,axiom,(
% 23.65/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f27,plain,(
% 23.65/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 23.65/3.49    inference(pure_predicate_removal,[],[f22])).
% 23.65/3.49  
% 23.65/3.49  fof(f48,plain,(
% 23.65/3.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.65/3.49    inference(ennf_transformation,[],[f27])).
% 23.65/3.49  
% 23.65/3.49  fof(f49,plain,(
% 23.65/3.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.65/3.49    inference(flattening,[],[f48])).
% 23.65/3.49  
% 23.65/3.49  fof(f113,plain,(
% 23.65/3.49    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f49])).
% 23.65/3.49  
% 23.65/3.49  fof(f20,axiom,(
% 23.65/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f28,plain,(
% 23.65/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 23.65/3.49    inference(pure_predicate_removal,[],[f20])).
% 23.65/3.49  
% 23.65/3.49  fof(f46,plain,(
% 23.65/3.49    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 23.65/3.49    inference(ennf_transformation,[],[f28])).
% 23.65/3.49  
% 23.65/3.49  fof(f111,plain,(
% 23.65/3.49    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f46])).
% 23.65/3.49  
% 23.65/3.49  fof(f116,plain,(
% 23.65/3.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f69])).
% 23.65/3.49  
% 23.65/3.49  fof(f144,plain,(
% 23.65/3.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.65/3.49    inference(equality_resolution,[],[f116])).
% 23.65/3.49  
% 23.65/3.49  fof(f115,plain,(
% 23.65/3.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f68])).
% 23.65/3.49  
% 23.65/3.49  fof(f141,plain,(
% 23.65/3.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.65/3.49    inference(equality_resolution,[],[f115])).
% 23.65/3.49  
% 23.65/3.49  fof(f1,axiom,(
% 23.65/3.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f30,plain,(
% 23.65/3.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.65/3.49    inference(ennf_transformation,[],[f1])).
% 23.65/3.49  
% 23.65/3.49  fof(f56,plain,(
% 23.65/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.65/3.49    inference(nnf_transformation,[],[f30])).
% 23.65/3.49  
% 23.65/3.49  fof(f57,plain,(
% 23.65/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.65/3.49    inference(rectify,[],[f56])).
% 23.65/3.49  
% 23.65/3.49  fof(f58,plain,(
% 23.65/3.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.65/3.49    introduced(choice_axiom,[])).
% 23.65/3.49  
% 23.65/3.49  fof(f59,plain,(
% 23.65/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.65/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f57,f58])).
% 23.65/3.49  
% 23.65/3.49  fof(f78,plain,(
% 23.65/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f59])).
% 23.65/3.49  
% 23.65/3.49  fof(f105,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f66])).
% 23.65/3.49  
% 23.65/3.49  fof(f137,plain,(
% 23.65/3.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 23.65/3.49    inference(equality_resolution,[],[f105])).
% 23.65/3.49  
% 23.65/3.49  fof(f11,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f35,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 23.65/3.49    inference(ennf_transformation,[],[f11])).
% 23.65/3.49  
% 23.65/3.49  fof(f94,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f35])).
% 23.65/3.49  
% 23.65/3.49  fof(f10,axiom,(
% 23.65/3.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f33,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 23.65/3.49    inference(ennf_transformation,[],[f10])).
% 23.65/3.49  
% 23.65/3.49  fof(f34,plain,(
% 23.65/3.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 23.65/3.49    inference(flattening,[],[f33])).
% 23.65/3.49  
% 23.65/3.49  fof(f93,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f34])).
% 23.65/3.49  
% 23.65/3.49  fof(f106,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f66])).
% 23.65/3.49  
% 23.65/3.49  fof(f135,plain,(
% 23.65/3.49    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.65/3.49    inference(equality_resolution,[],[f106])).
% 23.65/3.49  
% 23.65/3.49  fof(f136,plain,(
% 23.65/3.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 23.65/3.49    inference(equality_resolution,[],[f135])).
% 23.65/3.49  
% 23.65/3.49  fof(f16,axiom,(
% 23.65/3.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 23.65/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.65/3.49  
% 23.65/3.49  fof(f40,plain,(
% 23.65/3.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 23.65/3.49    inference(ennf_transformation,[],[f16])).
% 23.65/3.49  
% 23.65/3.49  fof(f41,plain,(
% 23.65/3.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 23.65/3.49    inference(flattening,[],[f40])).
% 23.65/3.49  
% 23.65/3.49  fof(f100,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 23.65/3.49    inference(cnf_transformation,[],[f41])).
% 23.65/3.49  
% 23.65/3.49  fof(f102,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f66])).
% 23.65/3.49  
% 23.65/3.49  fof(f139,plain,(
% 23.65/3.49    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 23.65/3.49    inference(equality_resolution,[],[f102])).
% 23.65/3.49  
% 23.65/3.49  fof(f103,plain,(
% 23.65/3.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.65/3.49    inference(cnf_transformation,[],[f66])).
% 23.65/3.49  
% 23.65/3.49  cnf(c_44,negated_conjecture,
% 23.65/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
% 23.65/3.49      inference(cnf_transformation,[],[f127]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2978,plain,
% 23.65/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_29,plain,
% 23.65/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | k1_relset_1(X1,X2,X0) = X1
% 23.65/3.49      | k1_xboole_0 = X2 ),
% 23.65/3.49      inference(cnf_transformation,[],[f101]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2989,plain,
% 23.65/3.49      ( k1_relset_1(X0,X1,X2) = X0
% 23.65/3.49      | k1_xboole_0 = X1
% 23.65/3.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 23.65/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8568,plain,
% 23.65/3.49      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2978,c_2989]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_21,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f98]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2995,plain,
% 23.65/3.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 23.65/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5729,plain,
% 23.65/3.49      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2978,c_2995]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8586,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_8568,c_5729]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_45,negated_conjecture,
% 23.65/3.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
% 23.65/3.49      inference(cnf_transformation,[],[f126]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8614,plain,
% 23.65/3.49      ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_8586]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12496,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_8586,c_45,c_8614]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12497,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_12496]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12,plain,
% 23.65/3.49      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f88]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3002,plain,
% 23.65/3.49      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_39,plain,
% 23.65/3.49      ( v5_pre_topc(X0,X1,X2)
% 23.65/3.49      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 23.65/3.49      | ~ v2_pre_topc(X1)
% 23.65/3.49      | ~ v2_pre_topc(X2)
% 23.65/3.49      | ~ l1_pre_topc(X1)
% 23.65/3.49      | ~ l1_pre_topc(X2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f143]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2982,plain,
% 23.65/3.49      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 23.65/3.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 23.65/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 23.65/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 23.65/3.49      | v2_pre_topc(X1) != iProver_top
% 23.65/3.49      | v2_pre_topc(X2) != iProver_top
% 23.65/3.49      | l1_pre_topc(X1) != iProver_top
% 23.65/3.49      | l1_pre_topc(X2) != iProver_top
% 23.65/3.49      | v1_funct_1(X0) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_6152,plain,
% 23.65/3.49      ( v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),X0,X1) = iProver_top
% 23.65/3.49      | v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 23.65/3.49      | v1_funct_2(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 23.65/3.49      | v2_pre_topc(X1) != iProver_top
% 23.65/3.49      | v2_pre_topc(X0) != iProver_top
% 23.65/3.49      | l1_pre_topc(X1) != iProver_top
% 23.65/3.49      | l1_pre_topc(X0) != iProver_top
% 23.65/3.49      | v1_funct_1(sK1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3002,c_2982]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_23564,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) = iProver_top
% 23.65/3.49      | v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)) != iProver_top
% 23.65/3.49      | v1_funct_2(sK1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)))) != iProver_top
% 23.65/3.49      | v2_pre_topc(X0) != iProver_top
% 23.65/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | l1_pre_topc(X0) != iProver_top
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | v1_funct_1(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_12497,c_6152]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9,plain,
% 23.65/3.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 23.65/3.49      inference(cnf_transformation,[],[f134]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_23859,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) = iProver_top
% 23.65/3.49      | v5_pre_topc(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)) != iProver_top
% 23.65/3.49      | v1_funct_2(sK1(k1_xboole_0),k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)))) != iProver_top
% 23.65/3.49      | v2_pre_topc(X0) != iProver_top
% 23.65/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | l1_pre_topc(X0) != iProver_top
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | v1_funct_1(sK1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_23564,c_9]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_32,plain,
% 23.65/3.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 23.65/3.49      inference(cnf_transformation,[],[f110]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_91,plain,
% 23.65/3.49      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_32]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_13,plain,
% 23.65/3.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f90]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_142,plain,
% 23.65/3.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_13]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_10,plain,
% 23.65/3.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 23.65/3.49      | k1_xboole_0 = X1
% 23.65/3.49      | k1_xboole_0 = X0 ),
% 23.65/3.49      inference(cnf_transformation,[],[f85]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_150,plain,
% 23.65/3.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 23.65/3.49      | k1_xboole_0 = k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_10]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_151,plain,
% 23.65/3.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_9]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3,plain,
% 23.65/3.49      ( v1_xboole_0(k1_xboole_0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f80]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_26,plain,
% 23.65/3.49      ( v1_funct_2(X0,k1_xboole_0,X1)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 23.65/3.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 23.65/3.49      inference(cnf_transformation,[],[f138]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3474,plain,
% 23.65/3.49      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
% 23.65/3.49      | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 23.65/3.49      | k1_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0)) != k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_26]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2988,plain,
% 23.65/3.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5728,plain,
% 23.65/3.49      ( k1_relset_1(X0,X0,k6_partfun1(X0)) = k1_relat_1(k6_partfun1(X0)) ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2988,c_2995]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_19,plain,
% 23.65/3.49      ( v4_relat_1(X0,X1)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 23.65/3.49      inference(cnf_transformation,[],[f96]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_31,plain,
% 23.65/3.49      ( ~ v1_partfun1(X0,X1)
% 23.65/3.49      | ~ v4_relat_1(X0,X1)
% 23.65/3.49      | ~ v1_relat_1(X0)
% 23.65/3.49      | k1_relat_1(X0) = X1 ),
% 23.65/3.49      inference(cnf_transformation,[],[f107]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_675,plain,
% 23.65/3.49      ( ~ v1_partfun1(X0,X1)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | ~ v1_relat_1(X0)
% 23.65/3.49      | k1_relat_1(X0) = X1 ),
% 23.65/3.49      inference(resolution,[status(thm)],[c_19,c_31]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_18,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | v1_relat_1(X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f95]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_679,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | ~ v1_partfun1(X0,X1)
% 23.65/3.49      | k1_relat_1(X0) = X1 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_675,c_31,c_19,c_18]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_680,plain,
% 23.65/3.49      ( ~ v1_partfun1(X0,X1)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | k1_relat_1(X0) = X1 ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_679]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_33,plain,
% 23.65/3.49      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f109]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_743,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | X3 != X1
% 23.65/3.49      | k6_partfun1(X3) != X0
% 23.65/3.49      | k1_relat_1(X0) = X1 ),
% 23.65/3.49      inference(resolution_lifted,[status(thm)],[c_680,c_33]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_744,plain,
% 23.65/3.49      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.65/3.49      | k1_relat_1(k6_partfun1(X0)) = X0 ),
% 23.65/3.49      inference(unflattening,[status(thm)],[c_743]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2967,plain,
% 23.65/3.49      ( k1_relat_1(k6_partfun1(X0)) = X0
% 23.65/3.49      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4803,plain,
% 23.65/3.49      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2988,c_2967]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5746,plain,
% 23.65/3.49      ( k1_relset_1(X0,X0,k6_partfun1(X0)) = X0 ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_5728,c_4803]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5763,plain,
% 23.65/3.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_5746]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1959,plain,
% 23.65/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.65/3.49      | v1_funct_2(X3,X4,X5)
% 23.65/3.49      | X3 != X0
% 23.65/3.49      | X4 != X1
% 23.65/3.49      | X5 != X2 ),
% 23.65/3.49      theory(equality) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8551,plain,
% 23.65/3.49      ( v1_funct_2(X0,X1,X2)
% 23.65/3.49      | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
% 23.65/3.49      | X0 != k6_partfun1(k1_xboole_0)
% 23.65/3.49      | X1 != k1_xboole_0
% 23.65/3.49      | X2 != k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1959]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8553,plain,
% 23.65/3.49      ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
% 23.65/3.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 23.65/3.49      | k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 23.65/3.49      | k1_xboole_0 != k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_8551]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 23.65/3.49      inference(cnf_transformation,[],[f83]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9142,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,k6_partfun1(X1))
% 23.65/3.49      | ~ r1_tarski(k6_partfun1(X1),X0)
% 23.65/3.49      | X0 = k6_partfun1(X1) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_4]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9144,plain,
% 23.65/3.49      ( ~ r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)
% 23.65/3.49      | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))
% 23.65/3.49      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_9142]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12537,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_12497,c_2978]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8,plain,
% 23.65/3.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 23.65/3.49      inference(cnf_transformation,[],[f133]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12545,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_12537,c_8]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_13169,plain,
% 23.65/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_12545]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_38,plain,
% 23.65/3.49      ( ~ v5_pre_topc(X0,X1,X2)
% 23.65/3.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 23.65/3.49      | ~ v2_pre_topc(X1)
% 23.65/3.49      | ~ v2_pre_topc(X2)
% 23.65/3.49      | ~ l1_pre_topc(X1)
% 23.65/3.49      | ~ l1_pre_topc(X2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f142]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2983,plain,
% 23.65/3.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 23.65/3.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 23.65/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 23.65/3.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 23.65/3.49      | v2_pre_topc(X1) != iProver_top
% 23.65/3.49      | v2_pre_topc(X2) != iProver_top
% 23.65/3.49      | l1_pre_topc(X1) != iProver_top
% 23.65/3.49      | l1_pre_topc(X2) != iProver_top
% 23.65/3.49      | v1_funct_1(X0) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_6760,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 23.65/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK2) != iProver_top
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK2) != iProver_top
% 23.65/3.49      | v1_funct_1(sK5) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2978,c_2983]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_53,negated_conjecture,
% 23.65/3.49      ( v2_pre_topc(sK2) ),
% 23.65/3.49      inference(cnf_transformation,[],[f118]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_54,plain,
% 23.65/3.49      ( v2_pre_topc(sK2) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_52,negated_conjecture,
% 23.65/3.49      ( l1_pre_topc(sK2) ),
% 23.65/3.49      inference(cnf_transformation,[],[f119]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_55,plain,
% 23.65/3.49      ( l1_pre_topc(sK2) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_51,negated_conjecture,
% 23.65/3.49      ( v2_pre_topc(sK3) ),
% 23.65/3.49      inference(cnf_transformation,[],[f120]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_56,plain,
% 23.65/3.49      ( v2_pre_topc(sK3) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_50,negated_conjecture,
% 23.65/3.49      ( l1_pre_topc(sK3) ),
% 23.65/3.49      inference(cnf_transformation,[],[f121]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_57,plain,
% 23.65/3.49      ( l1_pre_topc(sK3) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_46,negated_conjecture,
% 23.65/3.49      ( v1_funct_1(sK5) ),
% 23.65/3.49      inference(cnf_transformation,[],[f125]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_61,plain,
% 23.65/3.49      ( v1_funct_1(sK5) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_62,plain,
% 23.65/3.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_63,plain,
% 23.65/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_42,negated_conjecture,
% 23.65/3.49      ( v5_pre_topc(sK4,sK2,sK3)
% 23.65/3.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 23.65/3.49      inference(cnf_transformation,[],[f129]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2979,plain,
% 23.65/3.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_43,negated_conjecture,
% 23.65/3.49      ( sK4 = sK5 ),
% 23.65/3.49      inference(cnf_transformation,[],[f128]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3135,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_2979,c_43]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_48,negated_conjecture,
% 23.65/3.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f123]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2974,plain,
% 23.65/3.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3040,plain,
% 23.65/3.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_2974,c_43]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_47,negated_conjecture,
% 23.65/3.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 23.65/3.49      inference(cnf_transformation,[],[f124]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2975,plain,
% 23.65/3.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3045,plain,
% 23.65/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_2975,c_43]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_41,negated_conjecture,
% 23.65/3.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 23.65/3.49      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 23.65/3.49      inference(cnf_transformation,[],[f130]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2980,plain,
% 23.65/3.49      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3140,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_2980,c_43]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_35,plain,
% 23.65/3.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 23.65/3.49      | ~ l1_pre_topc(X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f112]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3388,plain,
% 23.65/3.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 23.65/3.49      | ~ l1_pre_topc(sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_35]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3389,plain,
% 23.65/3.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 23.65/3.49      | l1_pre_topc(sK3) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_3388]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_36,plain,
% 23.65/3.49      ( ~ v2_pre_topc(X0)
% 23.65/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 23.65/3.49      | ~ l1_pre_topc(X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f113]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3412,plain,
% 23.65/3.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | ~ v2_pre_topc(sK3)
% 23.65/3.49      | ~ l1_pre_topc(sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_36]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3413,plain,
% 23.65/3.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 23.65/3.49      | v2_pre_topc(sK3) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK3) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_3412]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_34,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 23.65/3.49      inference(cnf_transformation,[],[f111]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3621,plain,
% 23.65/3.49      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_34]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3622,plain,
% 23.65/3.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_3621]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3606,plain,
% 23.65/3.49      ( v5_pre_topc(X0,sK2,X1)
% 23.65/3.49      | ~ v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 23.65/3.49      | ~ v2_pre_topc(X1)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(X1)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_39]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4089,plain,
% 23.65/3.49      ( ~ v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | v5_pre_topc(X0,sK2,sK3)
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.65/3.49      | ~ v2_pre_topc(sK3)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(sK3)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_3606]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4816,plain,
% 23.65/3.49      ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | v5_pre_topc(sK5,sK2,sK3)
% 23.65/3.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.65/3.49      | ~ v2_pre_topc(sK3)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(sK3)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(sK5) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_4089]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4817,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK3) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK2) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK3) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK2) != iProver_top
% 23.65/3.49      | v1_funct_1(sK5) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_4816]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_40,plain,
% 23.65/3.49      ( ~ v5_pre_topc(X0,X1,X2)
% 23.65/3.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 23.65/3.49      | ~ v2_pre_topc(X1)
% 23.65/3.49      | ~ v2_pre_topc(X2)
% 23.65/3.49      | ~ l1_pre_topc(X1)
% 23.65/3.49      | ~ l1_pre_topc(X2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f144]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3616,plain,
% 23.65/3.49      ( ~ v5_pre_topc(X0,sK2,X1)
% 23.65/3.49      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 23.65/3.49      | ~ v2_pre_topc(X1)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(X1)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_40]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4129,plain,
% 23.65/3.49      ( v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | ~ v5_pre_topc(X0,sK2,sK3)
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.65/3.49      | ~ v2_pre_topc(sK3)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(sK3)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_3616]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4840,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | ~ v5_pre_topc(sK5,sK2,sK3)
% 23.65/3.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.65/3.49      | ~ v2_pre_topc(sK3)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(sK3)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(sK5) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_4129]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4841,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK3) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK2) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK3) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK2) != iProver_top
% 23.65/3.49      | v1_funct_1(sK5) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_4840]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_37,plain,
% 23.65/3.49      ( v5_pre_topc(X0,X1,X2)
% 23.65/3.49      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 23.65/3.49      | ~ v2_pre_topc(X1)
% 23.65/3.49      | ~ v2_pre_topc(X2)
% 23.65/3.49      | ~ l1_pre_topc(X1)
% 23.65/3.49      | ~ l1_pre_topc(X2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(cnf_transformation,[],[f141]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3578,plain,
% 23.65/3.49      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)
% 23.65/3.49      | v5_pre_topc(X0,sK2,X1)
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 23.65/3.49      | ~ v2_pre_topc(X1)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(X1)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_37]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4012,plain,
% 23.65/3.49      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 23.65/3.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_3578]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5698,plain,
% 23.65/3.49      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 23.65/3.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(sK5) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_4012]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5699,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 23.65/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK2) != iProver_top
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK2) != iProver_top
% 23.65/3.49      | v1_funct_1(sK5) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_5698]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7101,plain,
% 23.65/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_6760,c_54,c_55,c_56,c_57,c_61,c_62,c_63,c_3135,c_3040,
% 23.65/3.49                 c_3045,c_3140,c_3389,c_3413,c_3622,c_4817,c_4841,c_5699]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7102,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_7101]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7105,plain,
% 23.65/3.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_7102,c_54,c_55,c_56,c_57,c_61,c_62,c_63,c_3135,c_3040,
% 23.65/3.49                 c_3045,c_3389,c_3413,c_3622,c_4841,c_5699]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12532,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_12497,c_7105]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12559,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_12532,c_8]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_13170,plain,
% 23.65/3.49      ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_12559]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1,plain,
% 23.65/3.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 23.65/3.49      inference(cnf_transformation,[],[f78]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_17009,plain,
% 23.65/3.49      ( r2_hidden(sK0(X0,k6_partfun1(X1)),X0)
% 23.65/3.49      | r1_tarski(X0,k6_partfun1(X1)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_17016,plain,
% 23.65/3.49      ( r2_hidden(sK0(k1_xboole_0,k6_partfun1(k1_xboole_0)),k1_xboole_0)
% 23.65/3.49      | r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_17009]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8569,plain,
% 23.65/3.49      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5) = u1_struct_0(sK2)
% 23.65/3.49      | u1_struct_0(sK3) = k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3045,c_2989]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5730,plain,
% 23.65/3.49      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3045,c_2995]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8579,plain,
% 23.65/3.49      ( u1_struct_0(sK3) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_8569,c_5730]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8737,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(sK3) = k1_xboole_0 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_8579,c_3040]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8738,plain,
% 23.65/3.49      ( u1_struct_0(sK3) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_8737]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8772,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),k1_xboole_0) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8738,c_3040]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_25,plain,
% 23.65/3.49      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 23.65/3.49      | k1_xboole_0 = X1
% 23.65/3.49      | k1_xboole_0 = X0 ),
% 23.65/3.49      inference(cnf_transformation,[],[f137]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2993,plain,
% 23.65/3.49      ( k1_xboole_0 = X0
% 23.65/3.49      | k1_xboole_0 = X1
% 23.65/3.49      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 23.65/3.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3159,plain,
% 23.65/3.49      ( k1_xboole_0 = X0
% 23.65/3.49      | k1_xboole_0 = X1
% 23.65/3.49      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_2993,c_8]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9239,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8772,c_3159]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8771,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8738,c_3045]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8779,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_8771,c_8]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9547,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0
% 23.65/3.49      | u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_9239,c_8779]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9548,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_9547]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2977,plain,
% 23.65/3.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12538,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_12497,c_2977]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_13212,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_12538,c_3159]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_14033,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_13212,c_12545]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_14034,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_14033]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_14038,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(g1_pre_topc(k1_relat_1(sK5),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_9548,c_14034]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_14075,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_14034,c_2977]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_14074,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_14034,c_2978]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9576,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_9548,c_7105]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_15908,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_14074,c_9576]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_15931,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_9548,c_15908]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_30275,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_14038,c_14075,c_15931]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_30373,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_30275,c_12538]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4395,plain,
% 23.65/3.49      ( r2_hidden(sK0(X0,sK5),X0) | r1_tarski(X0,sK5) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4402,plain,
% 23.65/3.49      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
% 23.65/3.49      | r1_tarski(k1_xboole_0,sK5) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_4395]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5539,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_4]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5541,plain,
% 23.65/3.49      ( ~ r1_tarski(sK5,k1_xboole_0)
% 23.65/3.49      | ~ r1_tarski(k1_xboole_0,sK5)
% 23.65/3.49      | sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_5539]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3009,plain,
% 23.65/3.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 23.65/3.49      | r1_tarski(X0,X1) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_17,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.65/3.49      | ~ r2_hidden(X2,X0)
% 23.65/3.49      | ~ v1_xboole_0(X1) ),
% 23.65/3.49      inference(cnf_transformation,[],[f94]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2997,plain,
% 23.65/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.65/3.49      | r2_hidden(X2,X0) != iProver_top
% 23.65/3.49      | v1_xboole_0(X1) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7446,plain,
% 23.65/3.49      ( r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2978,c_2997]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12531,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_12497,c_7446]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_12566,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_12531,c_8]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_162,plain,
% 23.65/3.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_13680,plain,
% 23.65/3.49      ( r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_12566,c_162]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_13681,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_13680]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_13688,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | r1_tarski(sK5,X0) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3009,c_13681]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_13689,plain,
% 23.65/3.49      ( r1_tarski(sK5,X0)
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_13688]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_13691,plain,
% 23.65/3.49      ( r1_tarski(sK5,k1_xboole_0)
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_13689]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_24807,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.65/3.49      | ~ r2_hidden(sK0(X0,sK5),X0)
% 23.65/3.49      | ~ v1_xboole_0(X1) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_17]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_24809,plain,
% 23.65/3.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 23.65/3.49      | ~ r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
% 23.65/3.49      | ~ v1_xboole_0(k1_xboole_0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_24807]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_31920,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_30373,c_142,c_3,c_4402,c_5541,c_13691,c_24809]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_31921,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_31920]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_6156,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK3) != iProver_top
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK3) != iProver_top
% 23.65/3.49      | v1_funct_1(sK5) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2978,c_2982]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3391,plain,
% 23.65/3.49      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 23.65/3.49      | ~ l1_pre_topc(sK2) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_35]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3392,plain,
% 23.65/3.49      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 23.65/3.49      | l1_pre_topc(sK2) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_3391]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3415,plain,
% 23.65/3.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(sK2) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_36]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3416,plain,
% 23.65/3.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 23.65/3.49      | v2_pre_topc(sK2) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK2) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_3415]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3629,plain,
% 23.65/3.49      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_34]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3630,plain,
% 23.65/3.49      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_3629]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3588,plain,
% 23.65/3.49      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1)
% 23.65/3.49      | ~ v5_pre_topc(X0,sK2,X1)
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 23.65/3.49      | ~ v2_pre_topc(X1)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(X1)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_38]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4042,plain,
% 23.65/3.49      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 23.65/3.49      | ~ v5_pre_topc(X0,sK2,sK3)
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.65/3.49      | ~ v2_pre_topc(sK3)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(sK3)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_3588]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4776,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 23.65/3.49      | ~ v5_pre_topc(sK5,sK2,sK3)
% 23.65/3.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 23.65/3.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.65/3.49      | ~ v2_pre_topc(sK3)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(sK3)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(sK5) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_4042]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4777,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK3) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK2) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK3) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK2) != iProver_top
% 23.65/3.49      | v1_funct_1(sK5) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_4776]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2981,plain,
% 23.65/3.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 23.65/3.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 23.65/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 23.65/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 23.65/3.49      | v2_pre_topc(X1) != iProver_top
% 23.65/3.49      | v2_pre_topc(X2) != iProver_top
% 23.65/3.49      | l1_pre_topc(X1) != iProver_top
% 23.65/3.49      | l1_pre_topc(X2) != iProver_top
% 23.65/3.49      | v1_funct_1(X0) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5378,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK3) != iProver_top
% 23.65/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK3) != iProver_top
% 23.65/3.49      | v1_funct_1(sK5) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2978,c_2981]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4002,plain,
% 23.65/3.49      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 23.65/3.49      | v5_pre_topc(X0,sK2,sK3)
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 23.65/3.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.65/3.49      | ~ v2_pre_topc(sK3)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(sK3)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(X0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_3578]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4752,plain,
% 23.65/3.49      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 23.65/3.49      | v5_pre_topc(sK5,sK2,sK3)
% 23.65/3.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 23.65/3.49      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 23.65/3.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 23.65/3.49      | ~ v2_pre_topc(sK3)
% 23.65/3.49      | ~ v2_pre_topc(sK2)
% 23.65/3.49      | ~ l1_pre_topc(sK3)
% 23.65/3.49      | ~ l1_pre_topc(sK2)
% 23.65/3.49      | ~ v1_funct_1(sK5) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_4002]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4753,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK3) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK2) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK3) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK2) != iProver_top
% 23.65/3.49      | v1_funct_1(sK5) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_4752]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5841,plain,
% 23.65/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_5378,c_54,c_55,c_56,c_57,c_61,c_62,c_3040,c_3045,
% 23.65/3.49                 c_3140,c_3392,c_3416,c_3630,c_4753]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5842,plain,
% 23.65/3.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_5841]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_6683,plain,
% 23.65/3.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_6156,c_54,c_55,c_56,c_57,c_61,c_62,c_3135,c_3040,
% 23.65/3.49                 c_3045,c_3392,c_3416,c_3630,c_4777,c_5842]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_6684,plain,
% 23.65/3.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_6683]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_32019,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_31921,c_6684]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_16,plain,
% 23.65/3.49      ( m1_subset_1(X0,X1)
% 23.65/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.65/3.49      | ~ r2_hidden(X0,X2) ),
% 23.65/3.49      inference(cnf_transformation,[],[f93]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2998,plain,
% 23.65/3.49      ( m1_subset_1(X0,X1) = iProver_top
% 23.65/3.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 23.65/3.49      | r2_hidden(X0,X2) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7516,plain,
% 23.65/3.49      ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) = iProver_top
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_2978,c_2998]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_30378,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | m1_subset_1(X0,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) = iProver_top
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_30275,c_7516]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_30444,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | m1_subset_1(X0,k1_xboole_0) = iProver_top
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_30378,c_9]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_141,plain,
% 23.65/3.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_143,plain,
% 23.65/3.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_141]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4401,plain,
% 23.65/3.49      ( r2_hidden(sK0(X0,sK5),X0) = iProver_top
% 23.65/3.49      | r1_tarski(X0,sK5) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_4395]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4403,plain,
% 23.65/3.49      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
% 23.65/3.49      | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_4401]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5540,plain,
% 23.65/3.49      ( sK5 = X0
% 23.65/3.49      | r1_tarski(X0,sK5) != iProver_top
% 23.65/3.49      | r1_tarski(sK5,X0) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_5539]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5542,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0
% 23.65/3.49      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 23.65/3.49      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_5540]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_24808,plain,
% 23.65/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.65/3.49      | r2_hidden(sK0(X0,sK5),X0) != iProver_top
% 23.65/3.49      | v1_xboole_0(X1) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_24807]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_24810,plain,
% 23.65/3.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.65/3.49      | r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top
% 23.65/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_24808]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_30379,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_30275,c_7446]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_30435,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_30379,c_9]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_35422,plain,
% 23.65/3.49      ( r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | u1_struct_0(sK2) = k1_xboole_0 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_30435,c_162]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_35423,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_35422]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_35431,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | r1_tarski(sK5,X0) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3009,c_35423]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_35433,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | sK5 = k1_xboole_0
% 23.65/3.49      | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_35431]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_35545,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_30444,c_143,c_162,c_4403,c_5542,c_24810,c_35433]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_35634,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_35545,c_7446]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7447,plain,
% 23.65/3.49      ( r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3045,c_2997]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_35636,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_35545,c_7447]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_35724,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0
% 23.65/3.49      | r2_hidden(X0,sK5) != iProver_top
% 23.65/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_35636,c_9]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_37770,plain,
% 23.65/3.49      ( r2_hidden(X0,sK5) != iProver_top | sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_35634,c_162,c_35724]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_37771,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0 | r2_hidden(X0,sK5) != iProver_top ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_37770]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_37778,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0 | r1_tarski(sK5,X0) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3009,c_37771]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_37779,plain,
% 23.65/3.49      ( r1_tarski(sK5,X0) | sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_37778]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_37781,plain,
% 23.65/3.49      ( r1_tarski(sK5,k1_xboole_0) | sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_37779]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_37900,plain,
% 23.65/3.49      ( sK5 = k1_xboole_0 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_32019,c_142,c_3,c_4402,c_5541,c_24809,c_37781]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_4800,plain,
% 23.65/3.49      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8,c_2988]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7518,plain,
% 23.65/3.49      ( m1_subset_1(X0,k1_xboole_0) = iProver_top
% 23.65/3.49      | r2_hidden(X0,k6_partfun1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_4800,c_2998]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7448,plain,
% 23.65/3.49      ( r2_hidden(X0,k6_partfun1(k1_xboole_0)) != iProver_top
% 23.65/3.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_4800,c_2997]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_53925,plain,
% 23.65/3.49      ( r2_hidden(X0,k6_partfun1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_7518,c_162,c_7448]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_53932,plain,
% 23.65/3.49      ( r1_tarski(k6_partfun1(k1_xboole_0),X0) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3009,c_53925]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_53933,plain,
% 23.65/3.49      ( r1_tarski(k6_partfun1(k1_xboole_0),X0) ),
% 23.65/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_53932]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_53935,plain,
% 23.65/3.49      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_53933]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_68428,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.65/3.49      | ~ r2_hidden(sK0(X0,k6_partfun1(X2)),X0)
% 23.65/3.49      | ~ v1_xboole_0(X1) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_17]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_68430,plain,
% 23.65/3.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 23.65/3.49      | ~ r2_hidden(sK0(k1_xboole_0,k6_partfun1(k1_xboole_0)),k1_xboole_0)
% 23.65/3.49      | ~ v1_xboole_0(k1_xboole_0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_68428]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_24,plain,
% 23.65/3.49      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 23.65/3.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 23.65/3.49      | k1_xboole_0 = X0 ),
% 23.65/3.49      inference(cnf_transformation,[],[f136]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2994,plain,
% 23.65/3.49      ( k1_xboole_0 = X0
% 23.65/3.49      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) = iProver_top
% 23.65/3.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3110,plain,
% 23.65/3.49      ( k1_xboole_0 = X0
% 23.65/3.49      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) = iProver_top
% 23.65/3.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_2994,c_8]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3001,plain,
% 23.65/3.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3114,plain,
% 23.65/3.49      ( k1_xboole_0 = X0
% 23.65/3.49      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) = iProver_top ),
% 23.65/3.49      inference(forward_subsumption_resolution,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_3110,c_3001]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8769,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))))) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8738,c_2978]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_22,plain,
% 23.65/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.65/3.49      | v1_partfun1(X0,X1)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | ~ v1_funct_1(X0)
% 23.65/3.49      | v1_xboole_0(X2) ),
% 23.65/3.49      inference(cnf_transformation,[],[f100]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_719,plain,
% 23.65/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 23.65/3.49      | ~ v1_funct_1(X0)
% 23.65/3.49      | v1_xboole_0(X2)
% 23.65/3.49      | k1_relat_1(X0) = X1 ),
% 23.65/3.49      inference(resolution,[status(thm)],[c_22,c_680]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_721,plain,
% 23.65/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | ~ v1_funct_2(X0,X1,X2)
% 23.65/3.49      | ~ v1_funct_1(X0)
% 23.65/3.49      | v1_xboole_0(X2)
% 23.65/3.49      | k1_relat_1(X0) = X1 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_719,c_31,c_22,c_19,c_18]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_722,plain,
% 23.65/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | ~ v1_funct_1(X0)
% 23.65/3.49      | v1_xboole_0(X2)
% 23.65/3.49      | k1_relat_1(X0) = X1 ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_721]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2968,plain,
% 23.65/3.49      ( k1_relat_1(X0) = X1
% 23.65/3.49      | v1_funct_2(X0,X1,X2) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.65/3.49      | v1_funct_1(X0) != iProver_top
% 23.65/3.49      | v1_xboole_0(X2) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9263,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_1(sK5) != iProver_top
% 23.65/3.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8769,c_2968]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_15735,plain,
% 23.65/3.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_12559,c_12545]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_15736,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_15735]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_15742,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),k1_xboole_0) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_12497,c_15736]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_16288,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_9263,c_8772,c_15742]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_16289,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_16288]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8761,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8738,c_6684]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8828,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_8761,c_8]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9475,plain,
% 23.65/3.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_8828,c_8779]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9476,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_9475]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_16326,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_16289,c_9476]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_20290,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | v1_funct_2(sK5,k1_relat_1(sK5),k1_xboole_0) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8738,c_16326]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_37944,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 23.65/3.49      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_37900,c_20290]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_40120,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 23.65/3.49      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3114,c_37944]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_38025,plain,
% 23.65/3.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_37900,c_2977]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_87473,plain,
% 23.65/3.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 23.65/3.49      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_40120,c_38025]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8565,plain,
% 23.65/3.49      ( k1_relset_1(X0,X1,k1_xboole_0) = X0
% 23.65/3.49      | k1_xboole_0 = X1
% 23.65/3.49      | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3001,c_2989]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5726,plain,
% 23.65/3.49      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_3001,c_2995]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8601,plain,
% 23.65/3.49      ( k1_relat_1(k1_xboole_0) = X0
% 23.65/3.49      | k1_xboole_0 = X1
% 23.65/3.49      | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_8565,c_5726]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_89885,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 23.65/3.49      | u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 23.65/3.49      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_87473,c_8601]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_91464,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 23.65/3.49      | k1_relat_1(k1_xboole_0) = k1_xboole_0
% 23.65/3.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 23.65/3.49      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 23.65/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
% 23.65/3.49      | v2_pre_topc(X1) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK3) != iProver_top
% 23.65/3.49      | l1_pre_topc(X1) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK3) != iProver_top
% 23.65/3.49      | v1_funct_1(X0) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_89885,c_2981]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_92741,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 23.65/3.49      | k1_relat_1(k1_xboole_0) = k1_xboole_0
% 23.65/3.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 23.65/3.49      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 23.65/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 23.65/3.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 23.65/3.49      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 23.65/3.49      | v2_pre_topc(X1) != iProver_top
% 23.65/3.49      | v2_pre_topc(sK3) != iProver_top
% 23.65/3.49      | l1_pre_topc(X1) != iProver_top
% 23.65/3.49      | l1_pre_topc(sK3) != iProver_top
% 23.65/3.49      | v1_funct_1(X0) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_91464,c_8]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5731,plain,
% 23.65/3.49      ( k1_relset_1(X0,k1_xboole_0,X1) = k1_relat_1(X1)
% 23.65/3.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8,c_2995]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9455,plain,
% 23.65/3.49      ( k1_relset_1(X0,k1_xboole_0,sK5) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8779,c_5731]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2992,plain,
% 23.65/3.49      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 23.65/3.49      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 23.65/3.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3152,plain,
% 23.65/3.49      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 23.65/3.49      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 23.65/3.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_2992,c_9]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_20775,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | k1_relat_1(sK5) != k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_9455,c_3152]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_90,plain,
% 23.65/3.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_92,plain,
% 23.65/3.49      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_90]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3476,plain,
% 23.65/3.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0)) != k1_xboole_0
% 23.65/3.49      | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top
% 23.65/3.49      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_3474]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_18024,plain,
% 23.65/3.49      ( ~ r1_tarski(X0,k6_partfun1(X1))
% 23.65/3.49      | ~ r1_tarski(k6_partfun1(X1),X0)
% 23.65/3.49      | k6_partfun1(X1) = X0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_4]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_18026,plain,
% 23.65/3.49      ( ~ r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)
% 23.65/3.49      | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))
% 23.65/3.49      | k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_18024]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_60354,plain,
% 23.65/3.49      ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
% 23.65/3.49      | v1_funct_2(sK5,X0,X1)
% 23.65/3.49      | X1 != k1_xboole_0
% 23.65/3.49      | X0 != k1_xboole_0
% 23.65/3.49      | sK5 != k6_partfun1(k1_xboole_0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_8551]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_60359,plain,
% 23.65/3.49      ( X0 != k1_xboole_0
% 23.65/3.49      | X1 != k1_xboole_0
% 23.65/3.49      | sK5 != k6_partfun1(k1_xboole_0)
% 23.65/3.49      | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,X1,X0) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_60354]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_60361,plain,
% 23.65/3.49      ( sK5 != k6_partfun1(k1_xboole_0)
% 23.65/3.49      | k1_xboole_0 != k1_xboole_0
% 23.65/3.49      | v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 23.65/3.49      | v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_60359]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1951,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5545,plain,
% 23.65/3.49      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1951]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_60355,plain,
% 23.65/3.49      ( k6_partfun1(k1_xboole_0) != X0
% 23.65/3.49      | sK5 != X0
% 23.65/3.49      | sK5 = k6_partfun1(k1_xboole_0) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_5545]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_60365,plain,
% 23.65/3.49      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 23.65/3.49      | sK5 = k6_partfun1(k1_xboole_0)
% 23.65/3.49      | sK5 != k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_60355]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_96428,plain,
% 23.65/3.49      ( v1_funct_2(sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_20775,c_92,c_142,c_150,c_151,c_3,c_3476,c_4402,c_5541,
% 23.65/3.49                 c_5763,c_17016,c_18026,c_24809,c_37781,c_53935,c_60361,
% 23.65/3.49                 c_60365,c_68430]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_96432,plain,
% 23.65/3.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_96428,c_37900]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_28,plain,
% 23.65/3.49      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 23.65/3.49      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 23.65/3.49      inference(cnf_transformation,[],[f139]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2990,plain,
% 23.65/3.49      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 23.65/3.49      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 23.65/3.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3145,plain,
% 23.65/3.49      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 23.65/3.49      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 23.65/3.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_2990,c_9]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_96437,plain,
% 23.65/3.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 23.65/3.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_96432,c_3145]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_96442,plain,
% 23.65/3.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 23.65/3.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_96437,c_5726]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_96447,plain,
% 23.65/3.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_92741,c_143,c_96442]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5732,plain,
% 23.65/3.49      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 23.65/3.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_9,c_2995]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_9454,plain,
% 23.65/3.49      ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_relat_1(sK5)
% 23.65/3.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_8779,c_5732]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_27,plain,
% 23.65/3.49      ( v1_funct_2(X0,X1,X2)
% 23.65/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.65/3.49      | k1_relset_1(X1,X2,X0) != X1
% 23.65/3.49      | k1_xboole_0 = X2 ),
% 23.65/3.49      inference(cnf_transformation,[],[f103]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_2991,plain,
% 23.65/3.49      ( k1_relset_1(X0,X1,X2) != X0
% 23.65/3.49      | k1_xboole_0 = X1
% 23.65/3.49      | v1_funct_2(X2,X0,X1) = iProver_top
% 23.65/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_20550,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | k1_relat_1(sK5) != k1_xboole_0
% 23.65/3.49      | k1_xboole_0 = X0
% 23.65/3.49      | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_9454,c_2991]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_20565,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | k1_relat_1(sK5) != k1_xboole_0
% 23.65/3.49      | k1_xboole_0 = X0
% 23.65/3.49      | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(light_normalisation,[status(thm)],[c_20550,c_9]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_20551,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | k1_relat_1(sK5) != k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
% 23.65/3.49      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_9454,c_3152]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_21678,plain,
% 23.65/3.49      ( v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top
% 23.65/3.49      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | k1_relat_1(sK5) != k1_xboole_0 ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_20565,c_8779,c_20551]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_21679,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 23.65/3.49      | k1_relat_1(sK5) != k1_xboole_0
% 23.65/3.49      | v1_funct_2(sK5,k1_xboole_0,X0) = iProver_top ),
% 23.65/3.49      inference(renaming,[status(thm)],[c_21678]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_37937,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 23.65/3.49      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 23.65/3.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_37900,c_21679]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_8622,plain,
% 23.65/3.49      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 23.65/3.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 23.65/3.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 23.65/3.49      inference(superposition,[status(thm)],[c_5726,c_3152]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_45007,plain,
% 23.65/3.49      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 23.65/3.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_37937,c_143,c_8622]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_96724,plain,
% 23.65/3.49      ( k1_xboole_0 != k1_xboole_0
% 23.65/3.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_96447,c_45007]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_96860,plain,
% 23.65/3.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 23.65/3.49      inference(equality_resolution_simp,[status(thm)],[c_96724]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_37945,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 23.65/3.49      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_37900,c_16326]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_96735,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0
% 23.65/3.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_96447,c_37945]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_96864,plain,
% 23.65/3.49      ( u1_struct_0(sK2) = k1_xboole_0 ),
% 23.65/3.49      inference(backward_subsumption_resolution,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_96860,c_96735]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_98654,plain,
% 23.65/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.65/3.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != X2
% 23.65/3.49      | u1_struct_0(sK2) != X1
% 23.65/3.49      | sK5 != X0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1959]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_98656,plain,
% 23.65/3.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 23.65/3.49      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 23.65/3.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != k1_xboole_0
% 23.65/3.49      | u1_struct_0(sK2) != k1_xboole_0
% 23.65/3.49      | sK5 != k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_98654]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_99312,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 23.65/3.49      inference(global_propositional_subsumption,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_23859,c_91,c_142,c_150,c_151,c_3,c_3474,c_4402,c_5541,
% 23.65/3.49                 c_5763,c_8553,c_9144,c_12497,c_13169,c_13170,c_17016,
% 23.65/3.49                 c_24809,c_37781,c_53935,c_68430,c_96864,c_98656]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_99314,plain,
% 23.65/3.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0 ),
% 23.65/3.49      inference(light_normalisation,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_99312,c_37900,c_96447]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_38016,plain,
% 23.65/3.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_37900,c_6684]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_39627,plain,
% 23.65/3.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 23.65/3.49      inference(forward_subsumption_resolution,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_38016,c_3001]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_99323,plain,
% 23.65/3.49      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top ),
% 23.65/3.49      inference(demodulation,[status(thm)],[c_99314,c_39627]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_11889,plain,
% 23.65/3.49      ( X0 != X1 | X0 = u1_struct_0(sK2) | u1_struct_0(sK2) != X1 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1951]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_11890,plain,
% 23.65/3.49      ( u1_struct_0(sK2) != k1_xboole_0
% 23.65/3.49      | k1_xboole_0 = u1_struct_0(sK2)
% 23.65/3.49      | k1_xboole_0 != k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_11889]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_1950,plain,( X0 = X0 ),theory(equality) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_6998,plain,
% 23.65/3.49      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1950]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3563,plain,
% 23.65/3.49      ( v1_funct_2(X0,X1,X2)
% 23.65/3.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.65/3.49      | X2 != u1_struct_0(sK3)
% 23.65/3.49      | X1 != u1_struct_0(sK2)
% 23.65/3.49      | X0 != sK4 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1959]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_6997,plain,
% 23.65/3.49      ( v1_funct_2(X0,X1,u1_struct_0(sK3))
% 23.65/3.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 23.65/3.49      | X1 != u1_struct_0(sK2)
% 23.65/3.49      | X0 != sK4
% 23.65/3.49      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_3563]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_6999,plain,
% 23.65/3.49      ( X0 != u1_struct_0(sK2)
% 23.65/3.49      | X1 != sK4
% 23.65/3.49      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 23.65/3.49      | v1_funct_2(X1,X0,u1_struct_0(sK3)) = iProver_top
% 23.65/3.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_6997]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_7001,plain,
% 23.65/3.49      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 23.65/3.49      | k1_xboole_0 != u1_struct_0(sK2)
% 23.65/3.49      | k1_xboole_0 != sK4
% 23.65/3.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.65/3.49      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) = iProver_top ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_6999]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3759,plain,
% 23.65/3.49      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1951]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5552,plain,
% 23.65/3.49      ( X0 = sK4 | X0 != sK5 | sK4 != sK5 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_3759]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_5553,plain,
% 23.65/3.49      ( sK4 != sK5 | k1_xboole_0 = sK4 | k1_xboole_0 != sK5 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_5552]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3713,plain,
% 23.65/3.49      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_1951]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_3714,plain,
% 23.65/3.49      ( sK5 != k1_xboole_0
% 23.65/3.49      | k1_xboole_0 = sK5
% 23.65/3.49      | k1_xboole_0 != k1_xboole_0 ),
% 23.65/3.49      inference(instantiation,[status(thm)],[c_3713]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(c_59,plain,
% 23.65/3.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 23.65/3.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 23.65/3.49  
% 23.65/3.49  cnf(contradiction,plain,
% 23.65/3.49      ( $false ),
% 23.65/3.49      inference(minisat,
% 23.65/3.49                [status(thm)],
% 23.65/3.49                [c_99323,c_96864,c_37900,c_11890,c_6998,c_7001,c_5553,
% 23.65/3.49                 c_3714,c_151,c_150,c_43,c_59]) ).
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.65/3.49  
% 23.65/3.49  ------                               Statistics
% 23.65/3.49  
% 23.65/3.49  ------ General
% 23.65/3.49  
% 23.65/3.49  abstr_ref_over_cycles:                  0
% 23.65/3.49  abstr_ref_under_cycles:                 0
% 23.65/3.49  gc_basic_clause_elim:                   0
% 23.65/3.49  forced_gc_time:                         0
% 23.65/3.49  parsing_time:                           0.013
% 23.65/3.49  unif_index_cands_time:                  0.
% 23.65/3.49  unif_index_add_time:                    0.
% 23.65/3.49  orderings_time:                         0.
% 23.65/3.49  out_proof_time:                         0.035
% 23.65/3.49  total_time:                             2.948
% 23.65/3.49  num_of_symbols:                         59
% 23.65/3.49  num_of_terms:                           46642
% 23.65/3.49  
% 23.65/3.49  ------ Preprocessing
% 23.65/3.49  
% 23.65/3.49  num_of_splits:                          0
% 23.65/3.49  num_of_split_atoms:                     0
% 23.65/3.49  num_of_reused_defs:                     0
% 23.65/3.49  num_eq_ax_congr_red:                    33
% 23.65/3.49  num_of_sem_filtered_clauses:            1
% 23.65/3.49  num_of_subtypes:                        0
% 23.65/3.49  monotx_restored_types:                  0
% 23.65/3.49  sat_num_of_epr_types:                   0
% 23.65/3.49  sat_num_of_non_cyclic_types:            0
% 23.65/3.49  sat_guarded_non_collapsed_types:        0
% 23.65/3.49  num_pure_diseq_elim:                    0
% 23.65/3.49  simp_replaced_by:                       0
% 23.65/3.49  res_preprocessed:                       231
% 23.65/3.49  prep_upred:                             0
% 23.65/3.49  prep_unflattend:                        26
% 23.65/3.49  smt_new_axioms:                         0
% 23.65/3.49  pred_elim_cands:                        9
% 23.65/3.49  pred_elim:                              3
% 23.65/3.49  pred_elim_cl:                           4
% 23.65/3.49  pred_elim_cycles:                       6
% 23.65/3.49  merged_defs:                            8
% 23.65/3.49  merged_defs_ncl:                        0
% 23.65/3.49  bin_hyper_res:                          8
% 23.65/3.49  prep_cycles:                            4
% 23.65/3.49  pred_elim_time:                         0.024
% 23.65/3.49  splitting_time:                         0.
% 23.65/3.49  sem_filter_time:                        0.
% 23.65/3.49  monotx_time:                            0.001
% 23.65/3.49  subtype_inf_time:                       0.
% 23.65/3.49  
% 23.65/3.49  ------ Problem properties
% 23.65/3.49  
% 23.65/3.49  clauses:                                48
% 23.65/3.49  conjectures:                            13
% 23.65/3.49  epr:                                    11
% 23.65/3.49  horn:                                   40
% 23.65/3.49  ground:                                 14
% 23.65/3.49  unary:                                  20
% 23.65/3.49  binary:                                 9
% 23.65/3.49  lits:                                   132
% 23.65/3.49  lits_eq:                                19
% 23.65/3.49  fd_pure:                                0
% 23.65/3.49  fd_pseudo:                              0
% 23.65/3.49  fd_cond:                                4
% 23.65/3.49  fd_pseudo_cond:                         2
% 23.65/3.49  ac_symbols:                             0
% 23.65/3.49  
% 23.65/3.49  ------ Propositional Solver
% 23.65/3.49  
% 23.65/3.49  prop_solver_calls:                      35
% 23.65/3.49  prop_fast_solver_calls:                 10588
% 23.65/3.49  smt_solver_calls:                       0
% 23.65/3.49  smt_fast_solver_calls:                  0
% 23.65/3.49  prop_num_of_clauses:                    21727
% 23.65/3.49  prop_preprocess_simplified:             40383
% 23.65/3.49  prop_fo_subsumed:                       1920
% 23.65/3.49  prop_solver_time:                       0.
% 23.65/3.49  smt_solver_time:                        0.
% 23.65/3.49  smt_fast_solver_time:                   0.
% 23.65/3.49  prop_fast_solver_time:                  0.
% 23.65/3.49  prop_unsat_core_time:                   0.002
% 23.65/3.49  
% 23.65/3.49  ------ QBF
% 23.65/3.49  
% 23.65/3.49  qbf_q_res:                              0
% 23.65/3.49  qbf_num_tautologies:                    0
% 23.65/3.49  qbf_prep_cycles:                        0
% 23.65/3.49  
% 23.65/3.49  ------ BMC1
% 23.65/3.49  
% 23.65/3.49  bmc1_current_bound:                     -1
% 23.65/3.49  bmc1_last_solved_bound:                 -1
% 23.65/3.49  bmc1_unsat_core_size:                   -1
% 23.65/3.49  bmc1_unsat_core_parents_size:           -1
% 23.65/3.49  bmc1_merge_next_fun:                    0
% 23.65/3.49  bmc1_unsat_core_clauses_time:           0.
% 23.65/3.49  
% 23.65/3.49  ------ Instantiation
% 23.65/3.49  
% 23.65/3.49  inst_num_of_clauses:                    162
% 23.65/3.49  inst_num_in_passive:                    39
% 23.65/3.49  inst_num_in_active:                     2570
% 23.65/3.49  inst_num_in_unprocessed:                26
% 23.65/3.49  inst_num_of_loops:                      3099
% 23.65/3.49  inst_num_of_learning_restarts:          1
% 23.65/3.49  inst_num_moves_active_passive:          526
% 23.65/3.49  inst_lit_activity:                      0
% 23.65/3.49  inst_lit_activity_moves:                1
% 23.65/3.49  inst_num_tautologies:                   0
% 23.65/3.49  inst_num_prop_implied:                  0
% 23.65/3.49  inst_num_existing_simplified:           0
% 23.65/3.49  inst_num_eq_res_simplified:             0
% 23.65/3.49  inst_num_child_elim:                    0
% 23.65/3.49  inst_num_of_dismatching_blockings:      2992
% 23.65/3.49  inst_num_of_non_proper_insts:           6210
% 23.65/3.49  inst_num_of_duplicates:                 0
% 23.65/3.49  inst_inst_num_from_inst_to_res:         0
% 23.65/3.49  inst_dismatching_checking_time:         0.
% 23.65/3.49  
% 23.65/3.49  ------ Resolution
% 23.65/3.49  
% 23.65/3.49  res_num_of_clauses:                     65
% 23.65/3.49  res_num_in_passive:                     65
% 23.65/3.49  res_num_in_active:                      0
% 23.65/3.49  res_num_of_loops:                       235
% 23.65/3.49  res_forward_subset_subsumed:            241
% 23.65/3.49  res_backward_subset_subsumed:           6
% 23.65/3.49  res_forward_subsumed:                   0
% 23.65/3.49  res_backward_subsumed:                  0
% 23.65/3.49  res_forward_subsumption_resolution:     1
% 23.65/3.49  res_backward_subsumption_resolution:    0
% 23.65/3.49  res_clause_to_clause_subsumption:       9014
% 23.65/3.49  res_orphan_elimination:                 0
% 23.65/3.49  res_tautology_del:                      321
% 23.65/3.49  res_num_eq_res_simplified:              0
% 23.65/3.49  res_num_sel_changes:                    0
% 23.65/3.49  res_moves_from_active_to_pass:          0
% 23.65/3.49  
% 23.65/3.49  ------ Superposition
% 23.65/3.49  
% 23.65/3.49  sup_time_total:                         0.
% 23.65/3.49  sup_time_generating:                    0.
% 23.65/3.49  sup_time_sim_full:                      0.
% 23.65/3.49  sup_time_sim_immed:                     0.
% 23.65/3.49  
% 23.65/3.49  sup_num_of_clauses:                     937
% 23.65/3.49  sup_num_in_active:                      123
% 23.65/3.49  sup_num_in_passive:                     814
% 23.65/3.49  sup_num_of_loops:                       619
% 23.65/3.49  sup_fw_superposition:                   2936
% 23.65/3.49  sup_bw_superposition:                   2191
% 23.65/3.49  sup_immediate_simplified:               2566
% 23.65/3.49  sup_given_eliminated:                   10
% 23.65/3.49  comparisons_done:                       0
% 23.65/3.49  comparisons_avoided:                    95
% 23.65/3.49  
% 23.65/3.49  ------ Simplifications
% 23.65/3.49  
% 23.65/3.49  
% 23.65/3.49  sim_fw_subset_subsumed:                 1777
% 23.65/3.49  sim_bw_subset_subsumed:                 291
% 23.65/3.49  sim_fw_subsumed:                        259
% 23.65/3.49  sim_bw_subsumed:                        67
% 23.65/3.49  sim_fw_subsumption_res:                 10
% 23.65/3.49  sim_bw_subsumption_res:                 2
% 23.65/3.49  sim_tautology_del:                      304
% 23.65/3.49  sim_eq_tautology_del:                   216
% 23.65/3.49  sim_eq_res_simp:                        1
% 23.65/3.49  sim_fw_demodulated:                     492
% 23.65/3.49  sim_bw_demodulated:                     440
% 23.65/3.49  sim_light_normalised:                   317
% 23.65/3.49  sim_joinable_taut:                      0
% 23.65/3.49  sim_joinable_simp:                      0
% 23.65/3.49  sim_ac_normalised:                      0
% 23.65/3.49  sim_smt_subsumption:                    0
% 23.65/3.49  
%------------------------------------------------------------------------------
