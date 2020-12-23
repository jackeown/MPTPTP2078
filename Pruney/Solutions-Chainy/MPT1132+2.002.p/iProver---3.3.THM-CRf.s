%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:46 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  158 (1523 expanded)
%              Number of clauses        :  106 ( 359 expanded)
%              Number of leaves         :   11 ( 455 expanded)
%              Depth                    :   18
%              Number of atoms          :  729 (17866 expanded)
%              Number of equality atoms :  185 (1677 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | v5_pre_topc(X2,X0,X1) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
          & v1_funct_1(X3) )
     => ( ( ~ v5_pre_topc(sK4,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK4,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK4 = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                | v5_pre_topc(X2,X0,X1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ v5_pre_topc(sK3,X0,X1) )
            & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK3,X0,X1) )
            & sK3 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
                  | ~ v5_pre_topc(X2,X0,sK2) )
                & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
                  | v5_pre_topc(X2,X0,sK2) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
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
                  ( ( ~ v5_pre_topc(X3,sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK1,X1) )
                  & ( v5_pre_topc(X3,sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK1,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ v5_pre_topc(sK3,sK1,sK2) )
    & ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | v5_pre_topc(sK3,sK1,sK2) )
    & sK3 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f29,f28,f27,f26])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,
    ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,
    ( ~ v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1107,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1792,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1107])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1114,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v5_pre_topc(X0_47,X0_48,X1_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | m1_subset_1(sK0(X0_48,X1_48,X0_47),k1_zfmisc_1(u1_struct_0(X1_48)))
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1786,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(sK0(X0_48,X1_48,X0_47),k1_zfmisc_1(u1_struct_0(X1_48))) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1114])).

cnf(c_2658,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1792,c_1786])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_25,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_27,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_31,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_32,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_48,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_50,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1112,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k1_zfmisc_1(X0_49)))
    | l1_pre_topc(g1_pre_topc(X0_49,X0_47)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2019,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48))) ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_2020,plain,
    ( m1_subset_1(u1_pre_topc(X0_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2019])).

cnf(c_2022,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_2960,plain,
    ( m1_subset_1(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2658,c_25,c_27,c_31,c_32,c_50,c_2022])).

cnf(c_2961,plain,
    ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_subset_1(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2960])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1117,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k8_relset_1(X0_49,X1_49,X0_47,X1_47) = k10_relat_1(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1783,plain,
    ( k8_relset_1(X0_49,X1_49,X0_47,X1_47) = k10_relat_1(X0_47,X1_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1117])).

cnf(c_2122,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK4,X0_47) = k10_relat_1(sK4,X0_47) ),
    inference(superposition,[status(thm)],[c_1792,c_1783])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1113,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ v5_pre_topc(X0_47,X0_48,X1_48)
    | ~ v4_pre_topc(X1_47,X1_48)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,X1_47),X0_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X1_48)))
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1787,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v5_pre_topc(X0_47,X0_48,X1_48) != iProver_top
    | v4_pre_topc(X1_47,X1_48) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,X1_47),X0_48) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X1_48))) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1113])).

cnf(c_2696,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_1787])).

cnf(c_8,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_342,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_343,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | v4_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_20])).

cnf(c_348,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_1097,plain,
    ( ~ v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v4_pre_topc(X0_47,sK2)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ),
    inference(subtyping,[status(esa)],[c_348])).

cnf(c_1183,plain,
    ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(X0_47,sK2) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_363,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_364,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_368,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_20])).

cnf(c_369,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_368])).

cnf(c_1096,plain,
    ( ~ v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_1186,plain,
    ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1104,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1795,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1104])).

cnf(c_13,negated_conjecture,
    ( sK3 = sK4 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1108,negated_conjecture,
    ( sK3 = sK4 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1820,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1795,c_1108])).

cnf(c_2123,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0_47) = k10_relat_1(sK4,X0_47) ),
    inference(superposition,[status(thm)],[c_1820,c_1783])).

cnf(c_2697,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | v4_pre_topc(X0_47,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2123,c_1787])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_300,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_301,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_301,c_20])).

cnf(c_306,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_305])).

cnf(c_1099,plain,
    ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v4_pre_topc(X0_47,sK2)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_306])).

cnf(c_1177,plain,
    ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v4_pre_topc(X0_47,sK2) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_321,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_322,plain,
    ( ~ v4_pre_topc(X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ v4_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_20])).

cnf(c_327,plain,
    ( ~ v4_pre_topc(X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_1098,plain,
    ( ~ v4_pre_topc(X0_47,sK2)
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_327])).

cnf(c_1180,plain,
    ( v4_pre_topc(X0_47,sK2) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1098])).

cnf(c_12,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1109,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1791,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_1835,plain,
    ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1791,c_1108])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1103,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1796,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1103])).

cnf(c_1817,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1796,c_1108])).

cnf(c_3082,plain,
    ( v4_pre_topc(X0_47,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2697,c_25,c_27,c_31,c_32,c_33,c_50,c_1177,c_1180,c_1835,c_1820,c_1817,c_2022,c_2696])).

cnf(c_3178,plain,
    ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2696,c_1183,c_1186,c_3082])).

cnf(c_3188,plain,
    ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v4_pre_topc(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2961,c_3178])).

cnf(c_2659,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_1786])).

cnf(c_2901,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2659,c_25,c_27,c_31,c_1817])).

cnf(c_2902,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2901])).

cnf(c_3091,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2902,c_3082])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1116,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v5_pre_topc(X0_47,X0_48,X1_48)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,sK0(X0_48,X1_48,X0_47)),X0_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1784,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,sK0(X0_48,X1_48,X0_47)),X0_48) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1116])).

cnf(c_2455,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2123,c_1784])).

cnf(c_3028,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2455,c_25,c_27,c_31,c_1820,c_1817])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1115,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v5_pre_topc(X0_47,X0_48,X1_48)
    | v4_pre_topc(sK0(X0_48,X1_48,X0_47),X1_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ l1_pre_topc(X0_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v1_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1785,plain,
    ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
    | v4_pre_topc(sK0(X0_48,X1_48,X0_47),X1_48) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1115])).

cnf(c_2532,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v4_pre_topc(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1792,c_1785])).

cnf(c_2953,plain,
    ( v4_pre_topc(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2532,c_25,c_27,c_31,c_32,c_50,c_2022])).

cnf(c_2954,plain,
    ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v4_pre_topc(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2953])).

cnf(c_2533,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_1785])).

cnf(c_2894,plain,
    ( v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2533,c_25,c_27,c_31,c_1817])).

cnf(c_2895,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2894])).

cnf(c_2454,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4)),sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_1784])).

cnf(c_11,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1110,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1790,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_1844,plain,
    ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1790,c_1108])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3188,c_3091,c_3028,c_2954,c_2895,c_2454,c_2022,c_1844,c_50,c_33,c_32,c_31,c_27,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.16/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.01  
% 2.16/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.01  
% 2.16/1.01  ------  iProver source info
% 2.16/1.01  
% 2.16/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.01  git: non_committed_changes: false
% 2.16/1.01  git: last_make_outside_of_git: false
% 2.16/1.01  
% 2.16/1.01  ------ 
% 2.16/1.01  
% 2.16/1.01  ------ Input Options
% 2.16/1.01  
% 2.16/1.01  --out_options                           all
% 2.16/1.01  --tptp_safe_out                         true
% 2.16/1.01  --problem_path                          ""
% 2.16/1.01  --include_path                          ""
% 2.16/1.01  --clausifier                            res/vclausify_rel
% 2.16/1.01  --clausifier_options                    --mode clausify
% 2.16/1.01  --stdin                                 false
% 2.16/1.01  --stats_out                             all
% 2.16/1.01  
% 2.16/1.01  ------ General Options
% 2.16/1.01  
% 2.16/1.01  --fof                                   false
% 2.16/1.01  --time_out_real                         305.
% 2.16/1.01  --time_out_virtual                      -1.
% 2.16/1.01  --symbol_type_check                     false
% 2.16/1.01  --clausify_out                          false
% 2.16/1.01  --sig_cnt_out                           false
% 2.16/1.01  --trig_cnt_out                          false
% 2.16/1.01  --trig_cnt_out_tolerance                1.
% 2.16/1.01  --trig_cnt_out_sk_spl                   false
% 2.16/1.01  --abstr_cl_out                          false
% 2.16/1.01  
% 2.16/1.01  ------ Global Options
% 2.16/1.01  
% 2.16/1.01  --schedule                              default
% 2.16/1.01  --add_important_lit                     false
% 2.16/1.01  --prop_solver_per_cl                    1000
% 2.16/1.01  --min_unsat_core                        false
% 2.16/1.01  --soft_assumptions                      false
% 2.16/1.01  --soft_lemma_size                       3
% 2.16/1.01  --prop_impl_unit_size                   0
% 2.16/1.01  --prop_impl_unit                        []
% 2.16/1.01  --share_sel_clauses                     true
% 2.16/1.01  --reset_solvers                         false
% 2.16/1.01  --bc_imp_inh                            [conj_cone]
% 2.16/1.01  --conj_cone_tolerance                   3.
% 2.16/1.01  --extra_neg_conj                        none
% 2.16/1.01  --large_theory_mode                     true
% 2.16/1.01  --prolific_symb_bound                   200
% 2.16/1.01  --lt_threshold                          2000
% 2.16/1.01  --clause_weak_htbl                      true
% 2.16/1.01  --gc_record_bc_elim                     false
% 2.16/1.01  
% 2.16/1.01  ------ Preprocessing Options
% 2.16/1.01  
% 2.16/1.01  --preprocessing_flag                    true
% 2.16/1.01  --time_out_prep_mult                    0.1
% 2.16/1.01  --splitting_mode                        input
% 2.16/1.01  --splitting_grd                         true
% 2.16/1.01  --splitting_cvd                         false
% 2.16/1.01  --splitting_cvd_svl                     false
% 2.16/1.01  --splitting_nvd                         32
% 2.16/1.01  --sub_typing                            true
% 2.16/1.01  --prep_gs_sim                           true
% 2.16/1.01  --prep_unflatten                        true
% 2.16/1.01  --prep_res_sim                          true
% 2.16/1.01  --prep_upred                            true
% 2.16/1.01  --prep_sem_filter                       exhaustive
% 2.16/1.01  --prep_sem_filter_out                   false
% 2.16/1.01  --pred_elim                             true
% 2.16/1.01  --res_sim_input                         true
% 2.16/1.01  --eq_ax_congr_red                       true
% 2.16/1.01  --pure_diseq_elim                       true
% 2.16/1.01  --brand_transform                       false
% 2.16/1.01  --non_eq_to_eq                          false
% 2.16/1.01  --prep_def_merge                        true
% 2.16/1.01  --prep_def_merge_prop_impl              false
% 2.16/1.01  --prep_def_merge_mbd                    true
% 2.16/1.01  --prep_def_merge_tr_red                 false
% 2.16/1.01  --prep_def_merge_tr_cl                  false
% 2.16/1.01  --smt_preprocessing                     true
% 2.16/1.01  --smt_ac_axioms                         fast
% 2.16/1.01  --preprocessed_out                      false
% 2.16/1.01  --preprocessed_stats                    false
% 2.16/1.01  
% 2.16/1.01  ------ Abstraction refinement Options
% 2.16/1.01  
% 2.16/1.01  --abstr_ref                             []
% 2.16/1.01  --abstr_ref_prep                        false
% 2.16/1.01  --abstr_ref_until_sat                   false
% 2.16/1.01  --abstr_ref_sig_restrict                funpre
% 2.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.01  --abstr_ref_under                       []
% 2.16/1.01  
% 2.16/1.01  ------ SAT Options
% 2.16/1.01  
% 2.16/1.01  --sat_mode                              false
% 2.16/1.01  --sat_fm_restart_options                ""
% 2.16/1.01  --sat_gr_def                            false
% 2.16/1.01  --sat_epr_types                         true
% 2.16/1.01  --sat_non_cyclic_types                  false
% 2.16/1.01  --sat_finite_models                     false
% 2.16/1.01  --sat_fm_lemmas                         false
% 2.16/1.01  --sat_fm_prep                           false
% 2.16/1.01  --sat_fm_uc_incr                        true
% 2.16/1.01  --sat_out_model                         small
% 2.16/1.01  --sat_out_clauses                       false
% 2.16/1.01  
% 2.16/1.01  ------ QBF Options
% 2.16/1.01  
% 2.16/1.01  --qbf_mode                              false
% 2.16/1.01  --qbf_elim_univ                         false
% 2.16/1.01  --qbf_dom_inst                          none
% 2.16/1.01  --qbf_dom_pre_inst                      false
% 2.16/1.01  --qbf_sk_in                             false
% 2.16/1.01  --qbf_pred_elim                         true
% 2.16/1.01  --qbf_split                             512
% 2.16/1.01  
% 2.16/1.01  ------ BMC1 Options
% 2.16/1.01  
% 2.16/1.01  --bmc1_incremental                      false
% 2.16/1.01  --bmc1_axioms                           reachable_all
% 2.16/1.01  --bmc1_min_bound                        0
% 2.16/1.01  --bmc1_max_bound                        -1
% 2.16/1.01  --bmc1_max_bound_default                -1
% 2.16/1.01  --bmc1_symbol_reachability              true
% 2.16/1.01  --bmc1_property_lemmas                  false
% 2.16/1.01  --bmc1_k_induction                      false
% 2.16/1.01  --bmc1_non_equiv_states                 false
% 2.16/1.01  --bmc1_deadlock                         false
% 2.16/1.01  --bmc1_ucm                              false
% 2.16/1.01  --bmc1_add_unsat_core                   none
% 2.16/1.01  --bmc1_unsat_core_children              false
% 2.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.01  --bmc1_out_stat                         full
% 2.16/1.01  --bmc1_ground_init                      false
% 2.16/1.01  --bmc1_pre_inst_next_state              false
% 2.16/1.01  --bmc1_pre_inst_state                   false
% 2.16/1.01  --bmc1_pre_inst_reach_state             false
% 2.16/1.01  --bmc1_out_unsat_core                   false
% 2.16/1.01  --bmc1_aig_witness_out                  false
% 2.16/1.01  --bmc1_verbose                          false
% 2.16/1.01  --bmc1_dump_clauses_tptp                false
% 2.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.01  --bmc1_dump_file                        -
% 2.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.01  --bmc1_ucm_extend_mode                  1
% 2.16/1.01  --bmc1_ucm_init_mode                    2
% 2.16/1.01  --bmc1_ucm_cone_mode                    none
% 2.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.01  --bmc1_ucm_relax_model                  4
% 2.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.01  --bmc1_ucm_layered_model                none
% 2.16/1.01  --bmc1_ucm_max_lemma_size               10
% 2.16/1.01  
% 2.16/1.01  ------ AIG Options
% 2.16/1.01  
% 2.16/1.01  --aig_mode                              false
% 2.16/1.01  
% 2.16/1.01  ------ Instantiation Options
% 2.16/1.01  
% 2.16/1.01  --instantiation_flag                    true
% 2.16/1.01  --inst_sos_flag                         false
% 2.16/1.01  --inst_sos_phase                        true
% 2.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.01  --inst_lit_sel_side                     num_symb
% 2.16/1.01  --inst_solver_per_active                1400
% 2.16/1.01  --inst_solver_calls_frac                1.
% 2.16/1.01  --inst_passive_queue_type               priority_queues
% 2.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.01  --inst_passive_queues_freq              [25;2]
% 2.16/1.01  --inst_dismatching                      true
% 2.16/1.01  --inst_eager_unprocessed_to_passive     true
% 2.16/1.01  --inst_prop_sim_given                   true
% 2.16/1.01  --inst_prop_sim_new                     false
% 2.16/1.01  --inst_subs_new                         false
% 2.16/1.01  --inst_eq_res_simp                      false
% 2.16/1.01  --inst_subs_given                       false
% 2.16/1.01  --inst_orphan_elimination               true
% 2.16/1.01  --inst_learning_loop_flag               true
% 2.16/1.01  --inst_learning_start                   3000
% 2.16/1.01  --inst_learning_factor                  2
% 2.16/1.01  --inst_start_prop_sim_after_learn       3
% 2.16/1.01  --inst_sel_renew                        solver
% 2.16/1.01  --inst_lit_activity_flag                true
% 2.16/1.01  --inst_restr_to_given                   false
% 2.16/1.01  --inst_activity_threshold               500
% 2.16/1.01  --inst_out_proof                        true
% 2.16/1.01  
% 2.16/1.01  ------ Resolution Options
% 2.16/1.01  
% 2.16/1.01  --resolution_flag                       true
% 2.16/1.01  --res_lit_sel                           adaptive
% 2.16/1.01  --res_lit_sel_side                      none
% 2.16/1.01  --res_ordering                          kbo
% 2.16/1.01  --res_to_prop_solver                    active
% 2.16/1.01  --res_prop_simpl_new                    false
% 2.16/1.01  --res_prop_simpl_given                  true
% 2.16/1.01  --res_passive_queue_type                priority_queues
% 2.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.01  --res_passive_queues_freq               [15;5]
% 2.16/1.01  --res_forward_subs                      full
% 2.16/1.01  --res_backward_subs                     full
% 2.16/1.01  --res_forward_subs_resolution           true
% 2.16/1.01  --res_backward_subs_resolution          true
% 2.16/1.01  --res_orphan_elimination                true
% 2.16/1.01  --res_time_limit                        2.
% 2.16/1.01  --res_out_proof                         true
% 2.16/1.01  
% 2.16/1.01  ------ Superposition Options
% 2.16/1.01  
% 2.16/1.01  --superposition_flag                    true
% 2.16/1.01  --sup_passive_queue_type                priority_queues
% 2.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.01  --demod_completeness_check              fast
% 2.16/1.01  --demod_use_ground                      true
% 2.16/1.01  --sup_to_prop_solver                    passive
% 2.16/1.01  --sup_prop_simpl_new                    true
% 2.16/1.01  --sup_prop_simpl_given                  true
% 2.16/1.01  --sup_fun_splitting                     false
% 2.16/1.01  --sup_smt_interval                      50000
% 2.16/1.01  
% 2.16/1.01  ------ Superposition Simplification Setup
% 2.16/1.01  
% 2.16/1.01  --sup_indices_passive                   []
% 2.16/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.01  --sup_full_bw                           [BwDemod]
% 2.16/1.01  --sup_immed_triv                        [TrivRules]
% 2.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.01  --sup_immed_bw_main                     []
% 2.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.01  
% 2.16/1.01  ------ Combination Options
% 2.16/1.01  
% 2.16/1.01  --comb_res_mult                         3
% 2.16/1.01  --comb_sup_mult                         2
% 2.16/1.01  --comb_inst_mult                        10
% 2.16/1.01  
% 2.16/1.01  ------ Debug Options
% 2.16/1.01  
% 2.16/1.01  --dbg_backtrace                         false
% 2.16/1.01  --dbg_dump_prop_clauses                 false
% 2.16/1.01  --dbg_dump_prop_clauses_file            -
% 2.16/1.01  --dbg_out_stat                          false
% 2.16/1.01  ------ Parsing...
% 2.16/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.01  
% 2.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 2.16/1.01  
% 2.16/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.01  
% 2.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.01  ------ Proving...
% 2.16/1.01  ------ Problem Properties 
% 2.16/1.01  
% 2.16/1.01  
% 2.16/1.01  clauses                                 26
% 2.16/1.01  conjectures                             11
% 2.16/1.01  EPR                                     5
% 2.16/1.01  Horn                                    23
% 2.16/1.01  unary                                   9
% 2.16/1.01  binary                                  5
% 2.16/1.01  lits                                    73
% 2.16/1.01  lits eq                                 2
% 2.16/1.01  fd_pure                                 0
% 2.16/1.01  fd_pseudo                               0
% 2.16/1.01  fd_cond                                 0
% 2.16/1.01  fd_pseudo_cond                          0
% 2.16/1.01  AC symbols                              0
% 2.16/1.01  
% 2.16/1.01  ------ Schedule dynamic 5 is on 
% 2.16/1.01  
% 2.16/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.01  
% 2.16/1.01  
% 2.16/1.01  ------ 
% 2.16/1.01  Current options:
% 2.16/1.01  ------ 
% 2.16/1.01  
% 2.16/1.01  ------ Input Options
% 2.16/1.01  
% 2.16/1.01  --out_options                           all
% 2.16/1.01  --tptp_safe_out                         true
% 2.16/1.01  --problem_path                          ""
% 2.16/1.01  --include_path                          ""
% 2.16/1.01  --clausifier                            res/vclausify_rel
% 2.16/1.01  --clausifier_options                    --mode clausify
% 2.16/1.01  --stdin                                 false
% 2.16/1.01  --stats_out                             all
% 2.16/1.01  
% 2.16/1.01  ------ General Options
% 2.16/1.01  
% 2.16/1.01  --fof                                   false
% 2.16/1.01  --time_out_real                         305.
% 2.16/1.01  --time_out_virtual                      -1.
% 2.16/1.01  --symbol_type_check                     false
% 2.16/1.01  --clausify_out                          false
% 2.16/1.01  --sig_cnt_out                           false
% 2.16/1.01  --trig_cnt_out                          false
% 2.16/1.01  --trig_cnt_out_tolerance                1.
% 2.16/1.01  --trig_cnt_out_sk_spl                   false
% 2.16/1.01  --abstr_cl_out                          false
% 2.16/1.01  
% 2.16/1.01  ------ Global Options
% 2.16/1.01  
% 2.16/1.01  --schedule                              default
% 2.16/1.01  --add_important_lit                     false
% 2.16/1.01  --prop_solver_per_cl                    1000
% 2.16/1.01  --min_unsat_core                        false
% 2.16/1.01  --soft_assumptions                      false
% 2.16/1.01  --soft_lemma_size                       3
% 2.16/1.01  --prop_impl_unit_size                   0
% 2.16/1.01  --prop_impl_unit                        []
% 2.16/1.01  --share_sel_clauses                     true
% 2.16/1.01  --reset_solvers                         false
% 2.16/1.01  --bc_imp_inh                            [conj_cone]
% 2.16/1.01  --conj_cone_tolerance                   3.
% 2.16/1.01  --extra_neg_conj                        none
% 2.16/1.01  --large_theory_mode                     true
% 2.16/1.01  --prolific_symb_bound                   200
% 2.16/1.01  --lt_threshold                          2000
% 2.16/1.01  --clause_weak_htbl                      true
% 2.16/1.01  --gc_record_bc_elim                     false
% 2.16/1.01  
% 2.16/1.01  ------ Preprocessing Options
% 2.16/1.01  
% 2.16/1.01  --preprocessing_flag                    true
% 2.16/1.01  --time_out_prep_mult                    0.1
% 2.16/1.01  --splitting_mode                        input
% 2.16/1.01  --splitting_grd                         true
% 2.16/1.01  --splitting_cvd                         false
% 2.16/1.01  --splitting_cvd_svl                     false
% 2.16/1.01  --splitting_nvd                         32
% 2.16/1.01  --sub_typing                            true
% 2.16/1.01  --prep_gs_sim                           true
% 2.16/1.01  --prep_unflatten                        true
% 2.16/1.01  --prep_res_sim                          true
% 2.16/1.01  --prep_upred                            true
% 2.16/1.01  --prep_sem_filter                       exhaustive
% 2.16/1.01  --prep_sem_filter_out                   false
% 2.16/1.01  --pred_elim                             true
% 2.16/1.01  --res_sim_input                         true
% 2.16/1.01  --eq_ax_congr_red                       true
% 2.16/1.01  --pure_diseq_elim                       true
% 2.16/1.01  --brand_transform                       false
% 2.16/1.01  --non_eq_to_eq                          false
% 2.16/1.01  --prep_def_merge                        true
% 2.16/1.01  --prep_def_merge_prop_impl              false
% 2.16/1.01  --prep_def_merge_mbd                    true
% 2.16/1.01  --prep_def_merge_tr_red                 false
% 2.16/1.01  --prep_def_merge_tr_cl                  false
% 2.16/1.01  --smt_preprocessing                     true
% 2.16/1.01  --smt_ac_axioms                         fast
% 2.16/1.01  --preprocessed_out                      false
% 2.16/1.01  --preprocessed_stats                    false
% 2.16/1.01  
% 2.16/1.01  ------ Abstraction refinement Options
% 2.16/1.01  
% 2.16/1.01  --abstr_ref                             []
% 2.16/1.01  --abstr_ref_prep                        false
% 2.16/1.01  --abstr_ref_until_sat                   false
% 2.16/1.01  --abstr_ref_sig_restrict                funpre
% 2.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.01  --abstr_ref_under                       []
% 2.16/1.01  
% 2.16/1.01  ------ SAT Options
% 2.16/1.01  
% 2.16/1.01  --sat_mode                              false
% 2.16/1.01  --sat_fm_restart_options                ""
% 2.16/1.01  --sat_gr_def                            false
% 2.16/1.01  --sat_epr_types                         true
% 2.16/1.01  --sat_non_cyclic_types                  false
% 2.16/1.01  --sat_finite_models                     false
% 2.16/1.01  --sat_fm_lemmas                         false
% 2.16/1.01  --sat_fm_prep                           false
% 2.16/1.01  --sat_fm_uc_incr                        true
% 2.16/1.01  --sat_out_model                         small
% 2.16/1.01  --sat_out_clauses                       false
% 2.16/1.01  
% 2.16/1.01  ------ QBF Options
% 2.16/1.01  
% 2.16/1.01  --qbf_mode                              false
% 2.16/1.01  --qbf_elim_univ                         false
% 2.16/1.01  --qbf_dom_inst                          none
% 2.16/1.01  --qbf_dom_pre_inst                      false
% 2.16/1.01  --qbf_sk_in                             false
% 2.16/1.01  --qbf_pred_elim                         true
% 2.16/1.01  --qbf_split                             512
% 2.16/1.01  
% 2.16/1.01  ------ BMC1 Options
% 2.16/1.01  
% 2.16/1.01  --bmc1_incremental                      false
% 2.16/1.01  --bmc1_axioms                           reachable_all
% 2.16/1.01  --bmc1_min_bound                        0
% 2.16/1.01  --bmc1_max_bound                        -1
% 2.16/1.01  --bmc1_max_bound_default                -1
% 2.16/1.01  --bmc1_symbol_reachability              true
% 2.16/1.01  --bmc1_property_lemmas                  false
% 2.16/1.01  --bmc1_k_induction                      false
% 2.16/1.01  --bmc1_non_equiv_states                 false
% 2.16/1.01  --bmc1_deadlock                         false
% 2.16/1.01  --bmc1_ucm                              false
% 2.16/1.01  --bmc1_add_unsat_core                   none
% 2.16/1.01  --bmc1_unsat_core_children              false
% 2.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.01  --bmc1_out_stat                         full
% 2.16/1.01  --bmc1_ground_init                      false
% 2.16/1.01  --bmc1_pre_inst_next_state              false
% 2.16/1.01  --bmc1_pre_inst_state                   false
% 2.16/1.01  --bmc1_pre_inst_reach_state             false
% 2.16/1.01  --bmc1_out_unsat_core                   false
% 2.16/1.01  --bmc1_aig_witness_out                  false
% 2.16/1.01  --bmc1_verbose                          false
% 2.16/1.01  --bmc1_dump_clauses_tptp                false
% 2.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.01  --bmc1_dump_file                        -
% 2.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.01  --bmc1_ucm_extend_mode                  1
% 2.16/1.01  --bmc1_ucm_init_mode                    2
% 2.16/1.01  --bmc1_ucm_cone_mode                    none
% 2.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.01  --bmc1_ucm_relax_model                  4
% 2.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.01  --bmc1_ucm_layered_model                none
% 2.16/1.01  --bmc1_ucm_max_lemma_size               10
% 2.16/1.01  
% 2.16/1.01  ------ AIG Options
% 2.16/1.01  
% 2.16/1.01  --aig_mode                              false
% 2.16/1.01  
% 2.16/1.01  ------ Instantiation Options
% 2.16/1.01  
% 2.16/1.01  --instantiation_flag                    true
% 2.16/1.01  --inst_sos_flag                         false
% 2.16/1.01  --inst_sos_phase                        true
% 2.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.01  --inst_lit_sel_side                     none
% 2.16/1.01  --inst_solver_per_active                1400
% 2.16/1.01  --inst_solver_calls_frac                1.
% 2.16/1.01  --inst_passive_queue_type               priority_queues
% 2.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.01  --inst_passive_queues_freq              [25;2]
% 2.16/1.01  --inst_dismatching                      true
% 2.16/1.01  --inst_eager_unprocessed_to_passive     true
% 2.16/1.01  --inst_prop_sim_given                   true
% 2.16/1.01  --inst_prop_sim_new                     false
% 2.16/1.01  --inst_subs_new                         false
% 2.16/1.01  --inst_eq_res_simp                      false
% 2.16/1.01  --inst_subs_given                       false
% 2.16/1.01  --inst_orphan_elimination               true
% 2.16/1.01  --inst_learning_loop_flag               true
% 2.16/1.01  --inst_learning_start                   3000
% 2.16/1.01  --inst_learning_factor                  2
% 2.16/1.01  --inst_start_prop_sim_after_learn       3
% 2.16/1.01  --inst_sel_renew                        solver
% 2.16/1.01  --inst_lit_activity_flag                true
% 2.16/1.01  --inst_restr_to_given                   false
% 2.16/1.01  --inst_activity_threshold               500
% 2.16/1.01  --inst_out_proof                        true
% 2.16/1.01  
% 2.16/1.01  ------ Resolution Options
% 2.16/1.01  
% 2.16/1.01  --resolution_flag                       false
% 2.16/1.01  --res_lit_sel                           adaptive
% 2.16/1.01  --res_lit_sel_side                      none
% 2.16/1.01  --res_ordering                          kbo
% 2.16/1.01  --res_to_prop_solver                    active
% 2.16/1.01  --res_prop_simpl_new                    false
% 2.16/1.01  --res_prop_simpl_given                  true
% 2.16/1.01  --res_passive_queue_type                priority_queues
% 2.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.01  --res_passive_queues_freq               [15;5]
% 2.16/1.01  --res_forward_subs                      full
% 2.16/1.01  --res_backward_subs                     full
% 2.16/1.01  --res_forward_subs_resolution           true
% 2.16/1.01  --res_backward_subs_resolution          true
% 2.16/1.01  --res_orphan_elimination                true
% 2.16/1.01  --res_time_limit                        2.
% 2.16/1.01  --res_out_proof                         true
% 2.16/1.01  
% 2.16/1.01  ------ Superposition Options
% 2.16/1.01  
% 2.16/1.01  --superposition_flag                    true
% 2.16/1.01  --sup_passive_queue_type                priority_queues
% 2.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.01  --demod_completeness_check              fast
% 2.16/1.01  --demod_use_ground                      true
% 2.16/1.01  --sup_to_prop_solver                    passive
% 2.16/1.01  --sup_prop_simpl_new                    true
% 2.16/1.01  --sup_prop_simpl_given                  true
% 2.16/1.01  --sup_fun_splitting                     false
% 2.16/1.01  --sup_smt_interval                      50000
% 2.16/1.01  
% 2.16/1.01  ------ Superposition Simplification Setup
% 2.16/1.01  
% 2.16/1.01  --sup_indices_passive                   []
% 2.16/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.01  --sup_full_bw                           [BwDemod]
% 2.16/1.01  --sup_immed_triv                        [TrivRules]
% 2.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.01  --sup_immed_bw_main                     []
% 2.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.01  
% 2.16/1.01  ------ Combination Options
% 2.16/1.01  
% 2.16/1.01  --comb_res_mult                         3
% 2.16/1.01  --comb_sup_mult                         2
% 2.16/1.01  --comb_inst_mult                        10
% 2.16/1.01  
% 2.16/1.01  ------ Debug Options
% 2.16/1.01  
% 2.16/1.01  --dbg_backtrace                         false
% 2.16/1.01  --dbg_dump_prop_clauses                 false
% 2.16/1.01  --dbg_dump_prop_clauses_file            -
% 2.16/1.01  --dbg_out_stat                          false
% 2.16/1.01  
% 2.16/1.01  
% 2.16/1.01  
% 2.16/1.01  
% 2.16/1.01  ------ Proving...
% 2.16/1.01  
% 2.16/1.01  
% 2.16/1.01  % SZS status Theorem for theBenchmark.p
% 2.16/1.01  
% 2.16/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/1.01  
% 2.16/1.01  fof(f6,conjecture,(
% 2.16/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.01  
% 2.16/1.01  fof(f7,negated_conjecture,(
% 2.16/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.16/1.02    inference(negated_conjecture,[],[f6])).
% 2.16/1.02  
% 2.16/1.02  fof(f16,plain,(
% 2.16/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.16/1.02    inference(ennf_transformation,[],[f7])).
% 2.16/1.02  
% 2.16/1.02  fof(f17,plain,(
% 2.16/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.16/1.02    inference(flattening,[],[f16])).
% 2.16/1.02  
% 2.16/1.02  fof(f24,plain,(
% 2.16/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.16/1.02    inference(nnf_transformation,[],[f17])).
% 2.16/1.02  
% 2.16/1.02  fof(f25,plain,(
% 2.16/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.16/1.02    inference(flattening,[],[f24])).
% 2.16/1.02  
% 2.16/1.02  fof(f29,plain,(
% 2.16/1.02    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK4,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK4,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK4 = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK4))) )),
% 2.16/1.02    introduced(choice_axiom,[])).
% 2.16/1.02  
% 2.16/1.02  fof(f28,plain,(
% 2.16/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK3,X0,X1)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK3,X0,X1)) & sK3 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 2.16/1.02    introduced(choice_axiom,[])).
% 2.16/1.02  
% 2.16/1.02  fof(f27,plain,(
% 2.16/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(X2,X0,sK2)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(X2,X0,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 2.16/1.02    introduced(choice_axiom,[])).
% 2.16/1.02  
% 2.16/1.02  fof(f26,plain,(
% 2.16/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK1,X1)) & (v5_pre_topc(X3,sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK1,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.16/1.02    introduced(choice_axiom,[])).
% 2.16/1.02  
% 2.16/1.02  fof(f30,plain,(
% 2.16/1.02    ((((~v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)) & (v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)) & sK3 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.16/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f29,f28,f27,f26])).
% 2.16/1.02  
% 2.16/1.02  fof(f51,plain,(
% 2.16/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f2,axiom,(
% 2.16/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 2.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f10,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.16/1.02    inference(ennf_transformation,[],[f2])).
% 2.16/1.02  
% 2.16/1.02  fof(f11,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.16/1.02    inference(flattening,[],[f10])).
% 2.16/1.02  
% 2.16/1.02  fof(f18,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.16/1.02    inference(nnf_transformation,[],[f11])).
% 2.16/1.02  
% 2.16/1.02  fof(f19,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.16/1.02    inference(rectify,[],[f18])).
% 2.16/1.02  
% 2.16/1.02  fof(f20,plain,(
% 2.16/1.02    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.16/1.02    introduced(choice_axiom,[])).
% 2.16/1.02  
% 2.16/1.02  fof(f21,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.16/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 2.16/1.02  
% 2.16/1.02  fof(f33,plain,(
% 2.16/1.02    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f21])).
% 2.16/1.02  
% 2.16/1.02  fof(f43,plain,(
% 2.16/1.02    l1_pre_topc(sK1)),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f45,plain,(
% 2.16/1.02    l1_pre_topc(sK2)),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f49,plain,(
% 2.16/1.02    v1_funct_1(sK4)),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f50,plain,(
% 2.16/1.02    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f4,axiom,(
% 2.16/1.02    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f13,plain,(
% 2.16/1.02    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.16/1.02    inference(ennf_transformation,[],[f4])).
% 2.16/1.02  
% 2.16/1.02  fof(f37,plain,(
% 2.16/1.02    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f13])).
% 2.16/1.02  
% 2.16/1.02  fof(f3,axiom,(
% 2.16/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f8,plain,(
% 2.16/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 2.16/1.02    inference(pure_predicate_removal,[],[f3])).
% 2.16/1.02  
% 2.16/1.02  fof(f12,plain,(
% 2.16/1.02    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.16/1.02    inference(ennf_transformation,[],[f8])).
% 2.16/1.02  
% 2.16/1.02  fof(f36,plain,(
% 2.16/1.02    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.16/1.02    inference(cnf_transformation,[],[f12])).
% 2.16/1.02  
% 2.16/1.02  fof(f1,axiom,(
% 2.16/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f9,plain,(
% 2.16/1.02    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/1.02    inference(ennf_transformation,[],[f1])).
% 2.16/1.02  
% 2.16/1.02  fof(f31,plain,(
% 2.16/1.02    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/1.02    inference(cnf_transformation,[],[f9])).
% 2.16/1.02  
% 2.16/1.02  fof(f32,plain,(
% 2.16/1.02    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f21])).
% 2.16/1.02  
% 2.16/1.02  fof(f5,axiom,(
% 2.16/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/1.02  
% 2.16/1.02  fof(f14,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.16/1.02    inference(ennf_transformation,[],[f5])).
% 2.16/1.02  
% 2.16/1.02  fof(f15,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/1.02    inference(flattening,[],[f14])).
% 2.16/1.02  
% 2.16/1.02  fof(f22,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/1.02    inference(nnf_transformation,[],[f15])).
% 2.16/1.02  
% 2.16/1.02  fof(f23,plain,(
% 2.16/1.02    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/1.02    inference(flattening,[],[f22])).
% 2.16/1.02  
% 2.16/1.02  fof(f40,plain,(
% 2.16/1.02    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f23])).
% 2.16/1.02  
% 2.16/1.02  fof(f44,plain,(
% 2.16/1.02    v2_pre_topc(sK2)),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f41,plain,(
% 2.16/1.02    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f23])).
% 2.16/1.02  
% 2.16/1.02  fof(f48,plain,(
% 2.16/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f52,plain,(
% 2.16/1.02    sK3 = sK4),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f38,plain,(
% 2.16/1.02    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f23])).
% 2.16/1.02  
% 2.16/1.02  fof(f39,plain,(
% 2.16/1.02    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f23])).
% 2.16/1.02  
% 2.16/1.02  fof(f53,plain,(
% 2.16/1.02    v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f47,plain,(
% 2.16/1.02    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  fof(f35,plain,(
% 2.16/1.02    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f21])).
% 2.16/1.02  
% 2.16/1.02  fof(f34,plain,(
% 2.16/1.02    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v4_pre_topc(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.16/1.02    inference(cnf_transformation,[],[f21])).
% 2.16/1.02  
% 2.16/1.02  fof(f54,plain,(
% 2.16/1.02    ~v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)),
% 2.16/1.02    inference(cnf_transformation,[],[f30])).
% 2.16/1.02  
% 2.16/1.02  cnf(c_14,negated_conjecture,
% 2.16/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
% 2.16/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1107,negated_conjecture,
% 2.16/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1792,plain,
% 2.16/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1107]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3,plain,
% 2.16/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.16/1.02      | v5_pre_topc(X0,X1,X2)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.16/1.02      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 2.16/1.02      | ~ l1_pre_topc(X2)
% 2.16/1.02      | ~ l1_pre_topc(X1)
% 2.16/1.02      | ~ v1_funct_1(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1114,plain,
% 2.16/1.02      ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.16/1.02      | v5_pre_topc(X0_47,X0_48,X1_48)
% 2.16/1.02      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.16/1.02      | m1_subset_1(sK0(X0_48,X1_48,X0_47),k1_zfmisc_1(u1_struct_0(X1_48)))
% 2.16/1.02      | ~ l1_pre_topc(X0_48)
% 2.16/1.02      | ~ l1_pre_topc(X1_48)
% 2.16/1.02      | ~ v1_funct_1(X0_47) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1786,plain,
% 2.16/1.02      ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.16/1.02      | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.16/1.02      | m1_subset_1(sK0(X0_48,X1_48,X0_47),k1_zfmisc_1(u1_struct_0(X1_48))) = iProver_top
% 2.16/1.02      | l1_pre_topc(X1_48) != iProver_top
% 2.16/1.02      | l1_pre_topc(X0_48) != iProver_top
% 2.16/1.02      | v1_funct_1(X0_47) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1114]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2658,plain,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.16/1.02      | m1_subset_1(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
% 2.16/1.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.16/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_1792,c_1786]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_22,negated_conjecture,
% 2.16/1.02      ( l1_pre_topc(sK1) ),
% 2.16/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_25,plain,
% 2.16/1.02      ( l1_pre_topc(sK1) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_20,negated_conjecture,
% 2.16/1.02      ( l1_pre_topc(sK2) ),
% 2.16/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_27,plain,
% 2.16/1.02      ( l1_pre_topc(sK2) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_16,negated_conjecture,
% 2.16/1.02      ( v1_funct_1(sK4) ),
% 2.16/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_31,plain,
% 2.16/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_15,negated_conjecture,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
% 2.16/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_32,plain,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_6,plain,
% 2.16/1.02      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.16/1.02      | ~ l1_pre_topc(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_48,plain,
% 2.16/1.02      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.16/1.02      | l1_pre_topc(X0) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_50,plain,
% 2.16/1.02      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 2.16/1.02      | l1_pre_topc(sK2) != iProver_top ),
% 2.16/1.02      inference(instantiation,[status(thm)],[c_48]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_5,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.16/1.02      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.16/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1112,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k1_zfmisc_1(X0_49)))
% 2.16/1.02      | l1_pre_topc(g1_pre_topc(X0_49,X0_47)) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2019,plain,
% 2.16/1.02      ( ~ m1_subset_1(u1_pre_topc(X0_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48))))
% 2.16/1.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48))) ),
% 2.16/1.02      inference(instantiation,[status(thm)],[c_1112]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2020,plain,
% 2.16/1.02      ( m1_subset_1(u1_pre_topc(X0_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0_48)))) != iProver_top
% 2.16/1.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48))) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_2019]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2022,plain,
% 2.16/1.02      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 2.16/1.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 2.16/1.02      inference(instantiation,[status(thm)],[c_2020]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2960,plain,
% 2.16/1.02      ( m1_subset_1(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_2658,c_25,c_27,c_31,c_32,c_50,c_2022]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2961,plain,
% 2.16/1.02      ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.16/1.02      | m1_subset_1(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_2960]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_0,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/1.02      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.16/1.02      inference(cnf_transformation,[],[f31]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1117,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 2.16/1.02      | k8_relset_1(X0_49,X1_49,X0_47,X1_47) = k10_relat_1(X0_47,X1_47) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1783,plain,
% 2.16/1.02      ( k8_relset_1(X0_49,X1_49,X0_47,X1_47) = k10_relat_1(X0_47,X1_47)
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1117]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2122,plain,
% 2.16/1.02      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK4,X0_47) = k10_relat_1(sK4,X0_47) ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_1792,c_1783]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_4,plain,
% 2.16/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.16/1.02      | ~ v5_pre_topc(X0,X1,X2)
% 2.16/1.02      | ~ v4_pre_topc(X3,X2)
% 2.16/1.02      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.16/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.16/1.02      | ~ l1_pre_topc(X2)
% 2.16/1.02      | ~ l1_pre_topc(X1)
% 2.16/1.02      | ~ v1_funct_1(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f32]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1113,plain,
% 2.16/1.02      ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.16/1.02      | ~ v5_pre_topc(X0_47,X0_48,X1_48)
% 2.16/1.02      | ~ v4_pre_topc(X1_47,X1_48)
% 2.16/1.02      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,X1_47),X0_48)
% 2.16/1.02      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.16/1.02      | ~ m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X1_48)))
% 2.16/1.02      | ~ l1_pre_topc(X0_48)
% 2.16/1.02      | ~ l1_pre_topc(X1_48)
% 2.16/1.02      | ~ v1_funct_1(X0_47) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1787,plain,
% 2.16/1.02      ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.16/1.02      | v5_pre_topc(X0_47,X0_48,X1_48) != iProver_top
% 2.16/1.02      | v4_pre_topc(X1_47,X1_48) != iProver_top
% 2.16/1.02      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,X1_47),X0_48) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.16/1.02      | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X1_48))) != iProver_top
% 2.16/1.02      | l1_pre_topc(X1_48) != iProver_top
% 2.16/1.02      | l1_pre_topc(X0_48) != iProver_top
% 2.16/1.02      | v1_funct_1(X0_47) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1113]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2696,plain,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
% 2.16/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
% 2.16/1.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.16/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_2122,c_1787]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_8,plain,
% 2.16/1.02      ( v4_pre_topc(X0,X1)
% 2.16/1.02      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.16/1.02      | ~ v2_pre_topc(X1)
% 2.16/1.02      | ~ l1_pre_topc(X1) ),
% 2.16/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_21,negated_conjecture,
% 2.16/1.02      ( v2_pre_topc(sK2) ),
% 2.16/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_342,plain,
% 2.16/1.02      ( v4_pre_topc(X0,X1)
% 2.16/1.02      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.16/1.02      | ~ l1_pre_topc(X1)
% 2.16/1.02      | sK2 != X1 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_343,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 2.16/1.02      | v4_pre_topc(X0,sK2)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
% 2.16/1.02      | ~ l1_pre_topc(sK2) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_342]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_347,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
% 2.16/1.02      | v4_pre_topc(X0,sK2)
% 2.16/1.02      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_343,c_20]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_348,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 2.16/1.02      | v4_pre_topc(X0,sK2)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_347]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1097,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 2.16/1.02      | v4_pre_topc(X0_47,sK2)
% 2.16/1.02      | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_348]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1183,plain,
% 2.16/1.02      ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | v4_pre_topc(X0_47,sK2) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1097]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_7,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.16/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.16/1.02      | ~ v2_pre_topc(X1)
% 2.16/1.02      | ~ l1_pre_topc(X1) ),
% 2.16/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_363,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.16/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.16/1.02      | ~ l1_pre_topc(X1)
% 2.16/1.02      | sK2 != X1 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_364,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
% 2.16/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.16/1.02      | ~ l1_pre_topc(sK2) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_363]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_368,plain,
% 2.16/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
% 2.16/1.02      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_364,c_20]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_369,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
% 2.16/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_368]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1096,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 2.16/1.02      | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_369]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1186,plain,
% 2.16/1.02      ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_17,negated_conjecture,
% 2.16/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.16/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1104,negated_conjecture,
% 2.16/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1795,plain,
% 2.16/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1104]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_13,negated_conjecture,
% 2.16/1.02      ( sK3 = sK4 ),
% 2.16/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1108,negated_conjecture,
% 2.16/1.02      ( sK3 = sK4 ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1820,plain,
% 2.16/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.16/1.02      inference(light_normalisation,[status(thm)],[c_1795,c_1108]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2123,plain,
% 2.16/1.02      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0_47) = k10_relat_1(sK4,X0_47) ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_1820,c_1783]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2697,plain,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,sK2) != iProver_top
% 2.16/1.02      | v4_pre_topc(X0_47,sK2) != iProver_top
% 2.16/1.02      | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.16/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.16/1.02      | l1_pre_topc(sK2) != iProver_top
% 2.16/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.16/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_2123,c_1787]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_33,plain,
% 2.16/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_10,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,X1)
% 2.16/1.02      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.02      | ~ v2_pre_topc(X1)
% 2.16/1.02      | ~ l1_pre_topc(X1) ),
% 2.16/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_300,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,X1)
% 2.16/1.02      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.02      | ~ l1_pre_topc(X1)
% 2.16/1.02      | sK2 != X1 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_301,plain,
% 2.16/1.02      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 2.16/1.02      | ~ v4_pre_topc(X0,sK2)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.16/1.02      | ~ l1_pre_topc(sK2) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_300]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_305,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.16/1.02      | ~ v4_pre_topc(X0,sK2)
% 2.16/1.02      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_301,c_20]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_306,plain,
% 2.16/1.02      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 2.16/1.02      | ~ v4_pre_topc(X0,sK2)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_305]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1099,plain,
% 2.16/1.02      ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 2.16/1.02      | ~ v4_pre_topc(X0_47,sK2)
% 2.16/1.02      | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_306]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1177,plain,
% 2.16/1.02      ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.16/1.02      | v4_pre_topc(X0_47,sK2) != iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1099]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_9,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,X1)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.16/1.02      | ~ v2_pre_topc(X1)
% 2.16/1.02      | ~ l1_pre_topc(X1) ),
% 2.16/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_321,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,X1)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 2.16/1.02      | ~ l1_pre_topc(X1)
% 2.16/1.02      | sK2 != X1 ),
% 2.16/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_322,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,sK2)
% 2.16/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.16/1.02      | ~ l1_pre_topc(sK2) ),
% 2.16/1.02      inference(unflattening,[status(thm)],[c_321]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_326,plain,
% 2.16/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.16/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
% 2.16/1.02      | ~ v4_pre_topc(X0,sK2) ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_322,c_20]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_327,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0,sK2)
% 2.16/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_326]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1098,plain,
% 2.16/1.02      ( ~ v4_pre_topc(X0_47,sK2)
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
% 2.16/1.02      | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_327]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1180,plain,
% 2.16/1.02      ( v4_pre_topc(X0_47,sK2) != iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1098]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_12,negated_conjecture,
% 2.16/1.02      ( v5_pre_topc(sK3,sK1,sK2)
% 2.16/1.02      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 2.16/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1109,negated_conjecture,
% 2.16/1.02      ( v5_pre_topc(sK3,sK1,sK2)
% 2.16/1.02      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1791,plain,
% 2.16/1.02      ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1109]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1835,plain,
% 2.16/1.02      ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 2.16/1.02      inference(light_normalisation,[status(thm)],[c_1791,c_1108]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_18,negated_conjecture,
% 2.16/1.02      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.16/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1103,negated_conjecture,
% 2.16/1.02      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1796,plain,
% 2.16/1.02      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1103]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1817,plain,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.16/1.02      inference(light_normalisation,[status(thm)],[c_1796,c_1108]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3082,plain,
% 2.16/1.02      ( v4_pre_topc(X0_47,sK2) != iProver_top
% 2.16/1.02      | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_2697,c_25,c_27,c_31,c_32,c_33,c_50,c_1177,c_1180,
% 2.16/1.02                 c_1835,c_1820,c_1817,c_2022,c_2696]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3178,plain,
% 2.16/1.02      ( v4_pre_topc(X0_47,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | v4_pre_topc(k10_relat_1(sK4,X0_47),sK1) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) != iProver_top ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_2696,c_1183,c_1186,c_3082]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3188,plain,
% 2.16/1.02      ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.16/1.02      | v4_pre_topc(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4)),sK1) = iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_2961,c_3178]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2659,plain,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.16/1.02      | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.16/1.02      | l1_pre_topc(sK2) != iProver_top
% 2.16/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.16/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_1820,c_1786]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2901,plain,
% 2.16/1.02      ( m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_2659,c_25,c_27,c_31,c_1817]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2902,plain,
% 2.16/1.02      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.16/1.02      | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_2901]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3091,plain,
% 2.16/1.02      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.16/1.02      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) != iProver_top
% 2.16/1.02      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) = iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_2902,c_3082]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1,plain,
% 2.16/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.16/1.02      | v5_pre_topc(X0,X1,X2)
% 2.16/1.02      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.16/1.02      | ~ l1_pre_topc(X2)
% 2.16/1.02      | ~ l1_pre_topc(X1)
% 2.16/1.02      | ~ v1_funct_1(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1116,plain,
% 2.16/1.02      ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.16/1.02      | v5_pre_topc(X0_47,X0_48,X1_48)
% 2.16/1.02      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,sK0(X0_48,X1_48,X0_47)),X0_48)
% 2.16/1.02      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.16/1.02      | ~ l1_pre_topc(X0_48)
% 2.16/1.02      | ~ l1_pre_topc(X1_48)
% 2.16/1.02      | ~ v1_funct_1(X0_47) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1784,plain,
% 2.16/1.02      ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.16/1.02      | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
% 2.16/1.02      | v4_pre_topc(k8_relset_1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_47,sK0(X0_48,X1_48,X0_47)),X0_48) != iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.16/1.02      | l1_pre_topc(X1_48) != iProver_top
% 2.16/1.02      | l1_pre_topc(X0_48) != iProver_top
% 2.16/1.02      | v1_funct_1(X0_47) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1116]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2455,plain,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.16/1.02      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top
% 2.16/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.16/1.02      | l1_pre_topc(sK2) != iProver_top
% 2.16/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.16/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_2123,c_1784]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_3028,plain,
% 2.16/1.02      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.16/1.02      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,sK2,sK4)),sK1) != iProver_top ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_2455,c_25,c_27,c_31,c_1820,c_1817]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2,plain,
% 2.16/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.16/1.02      | v5_pre_topc(X0,X1,X2)
% 2.16/1.02      | v4_pre_topc(sK0(X1,X2,X0),X2)
% 2.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.16/1.02      | ~ l1_pre_topc(X2)
% 2.16/1.02      | ~ l1_pre_topc(X1)
% 2.16/1.02      | ~ v1_funct_1(X0) ),
% 2.16/1.02      inference(cnf_transformation,[],[f34]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1115,plain,
% 2.16/1.02      ( ~ v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 2.16/1.02      | v5_pre_topc(X0_47,X0_48,X1_48)
% 2.16/1.02      | v4_pre_topc(sK0(X0_48,X1_48,X0_47),X1_48)
% 2.16/1.02      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 2.16/1.02      | ~ l1_pre_topc(X0_48)
% 2.16/1.02      | ~ l1_pre_topc(X1_48)
% 2.16/1.02      | ~ v1_funct_1(X0_47) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1785,plain,
% 2.16/1.02      ( v1_funct_2(X0_47,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 2.16/1.02      | v5_pre_topc(X0_47,X0_48,X1_48) = iProver_top
% 2.16/1.02      | v4_pre_topc(sK0(X0_48,X1_48,X0_47),X1_48) = iProver_top
% 2.16/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 2.16/1.02      | l1_pre_topc(X1_48) != iProver_top
% 2.16/1.02      | l1_pre_topc(X0_48) != iProver_top
% 2.16/1.02      | v1_funct_1(X0_47) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1115]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2532,plain,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.16/1.02      | v4_pre_topc(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.16/1.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.16/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_1792,c_1785]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2953,plain,
% 2.16/1.02      ( v4_pre_topc(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_2532,c_25,c_27,c_31,c_32,c_50,c_2022]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2954,plain,
% 2.16/1.02      ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.16/1.02      | v4_pre_topc(sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_2953]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2533,plain,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.16/1.02      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
% 2.16/1.02      | l1_pre_topc(sK2) != iProver_top
% 2.16/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.16/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_1820,c_1785]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2894,plain,
% 2.16/1.02      ( v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 2.16/1.02      inference(global_propositional_subsumption,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_2533,c_25,c_27,c_31,c_1817]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2895,plain,
% 2.16/1.02      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 2.16/1.02      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top ),
% 2.16/1.02      inference(renaming,[status(thm)],[c_2894]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_2454,plain,
% 2.16/1.02      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.16/1.02      | v4_pre_topc(k10_relat_1(sK4,sK0(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK4)),sK1) != iProver_top
% 2.16/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
% 2.16/1.02      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | l1_pre_topc(sK1) != iProver_top
% 2.16/1.02      | v1_funct_1(sK4) != iProver_top ),
% 2.16/1.02      inference(superposition,[status(thm)],[c_2122,c_1784]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_11,negated_conjecture,
% 2.16/1.02      ( ~ v5_pre_topc(sK3,sK1,sK2)
% 2.16/1.02      | ~ v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 2.16/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1110,negated_conjecture,
% 2.16/1.02      ( ~ v5_pre_topc(sK3,sK1,sK2)
% 2.16/1.02      | ~ v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 2.16/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1790,plain,
% 2.16/1.02      ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 2.16/1.02      inference(predicate_to_equality,[status(thm)],[c_1110]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(c_1844,plain,
% 2.16/1.02      ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 2.16/1.02      | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
% 2.16/1.02      inference(light_normalisation,[status(thm)],[c_1790,c_1108]) ).
% 2.16/1.02  
% 2.16/1.02  cnf(contradiction,plain,
% 2.16/1.02      ( $false ),
% 2.16/1.02      inference(minisat,
% 2.16/1.02                [status(thm)],
% 2.16/1.02                [c_3188,c_3091,c_3028,c_2954,c_2895,c_2454,c_2022,c_1844,
% 2.16/1.02                 c_50,c_33,c_32,c_31,c_27,c_25]) ).
% 2.16/1.02  
% 2.16/1.02  
% 2.16/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.02  
% 2.16/1.02  ------                               Statistics
% 2.16/1.02  
% 2.16/1.02  ------ General
% 2.16/1.02  
% 2.16/1.02  abstr_ref_over_cycles:                  0
% 2.16/1.02  abstr_ref_under_cycles:                 0
% 2.16/1.02  gc_basic_clause_elim:                   0
% 2.16/1.02  forced_gc_time:                         0
% 2.16/1.02  parsing_time:                           0.013
% 2.16/1.02  unif_index_cands_time:                  0.
% 2.16/1.02  unif_index_add_time:                    0.
% 2.16/1.02  orderings_time:                         0.
% 2.16/1.02  out_proof_time:                         0.011
% 2.16/1.02  total_time:                             0.164
% 2.16/1.02  num_of_symbols:                         56
% 2.16/1.02  num_of_terms:                           2436
% 2.16/1.02  
% 2.16/1.02  ------ Preprocessing
% 2.16/1.02  
% 2.16/1.02  num_of_splits:                          0
% 2.16/1.02  num_of_split_atoms:                     0
% 2.16/1.02  num_of_reused_defs:                     0
% 2.16/1.02  num_eq_ax_congr_red:                    12
% 2.16/1.02  num_of_sem_filtered_clauses:            1
% 2.16/1.02  num_of_subtypes:                        3
% 2.16/1.02  monotx_restored_types:                  0
% 2.16/1.02  sat_num_of_epr_types:                   0
% 2.16/1.02  sat_num_of_non_cyclic_types:            0
% 2.16/1.02  sat_guarded_non_collapsed_types:        0
% 2.16/1.02  num_pure_diseq_elim:                    0
% 2.16/1.02  simp_replaced_by:                       0
% 2.16/1.02  res_preprocessed:                       109
% 2.16/1.02  prep_upred:                             0
% 2.16/1.02  prep_unflattend:                        24
% 2.16/1.02  smt_new_axioms:                         0
% 2.16/1.02  pred_elim_cands:                        7
% 2.16/1.02  pred_elim:                              1
% 2.16/1.02  pred_elim_cl:                           -2
% 2.16/1.02  pred_elim_cycles:                       3
% 2.16/1.02  merged_defs:                            6
% 2.16/1.02  merged_defs_ncl:                        0
% 2.16/1.02  bin_hyper_res:                          6
% 2.16/1.02  prep_cycles:                            3
% 2.16/1.02  pred_elim_time:                         0.023
% 2.16/1.02  splitting_time:                         0.
% 2.16/1.02  sem_filter_time:                        0.
% 2.16/1.02  monotx_time:                            0.
% 2.16/1.02  subtype_inf_time:                       0.
% 2.16/1.02  
% 2.16/1.02  ------ Problem properties
% 2.16/1.02  
% 2.16/1.02  clauses:                                26
% 2.16/1.02  conjectures:                            11
% 2.16/1.02  epr:                                    5
% 2.16/1.02  horn:                                   23
% 2.16/1.02  ground:                                 11
% 2.16/1.02  unary:                                  9
% 2.16/1.02  binary:                                 5
% 2.16/1.02  lits:                                   73
% 2.16/1.02  lits_eq:                                2
% 2.16/1.02  fd_pure:                                0
% 2.16/1.02  fd_pseudo:                              0
% 2.16/1.02  fd_cond:                                0
% 2.16/1.02  fd_pseudo_cond:                         0
% 2.16/1.02  ac_symbols:                             0
% 2.16/1.02  
% 2.16/1.02  ------ Propositional Solver
% 2.16/1.02  
% 2.16/1.02  prop_solver_calls:                      22
% 2.16/1.02  prop_fast_solver_calls:                 1033
% 2.16/1.02  smt_solver_calls:                       0
% 2.16/1.02  smt_fast_solver_calls:                  0
% 2.16/1.02  prop_num_of_clauses:                    861
% 2.16/1.02  prop_preprocess_simplified:             3554
% 2.16/1.02  prop_fo_subsumed:                       58
% 2.16/1.02  prop_solver_time:                       0.
% 2.16/1.02  smt_solver_time:                        0.
% 2.16/1.02  smt_fast_solver_time:                   0.
% 2.16/1.02  prop_fast_solver_time:                  0.
% 2.16/1.02  prop_unsat_core_time:                   0.
% 2.16/1.02  
% 2.16/1.02  ------ QBF
% 2.16/1.02  
% 2.16/1.02  qbf_q_res:                              0
% 2.16/1.02  qbf_num_tautologies:                    0
% 2.16/1.02  qbf_prep_cycles:                        0
% 2.16/1.02  
% 2.16/1.02  ------ BMC1
% 2.16/1.02  
% 2.16/1.02  bmc1_current_bound:                     -1
% 2.16/1.02  bmc1_last_solved_bound:                 -1
% 2.16/1.02  bmc1_unsat_core_size:                   -1
% 2.16/1.02  bmc1_unsat_core_parents_size:           -1
% 2.16/1.02  bmc1_merge_next_fun:                    0
% 2.16/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.02  
% 2.16/1.02  ------ Instantiation
% 2.16/1.02  
% 2.16/1.02  inst_num_of_clauses:                    227
% 2.16/1.02  inst_num_in_passive:                    44
% 2.16/1.02  inst_num_in_active:                     179
% 2.16/1.02  inst_num_in_unprocessed:                4
% 2.16/1.02  inst_num_of_loops:                      200
% 2.16/1.02  inst_num_of_learning_restarts:          0
% 2.16/1.02  inst_num_moves_active_passive:          17
% 2.16/1.02  inst_lit_activity:                      0
% 2.16/1.02  inst_lit_activity_moves:                0
% 2.16/1.02  inst_num_tautologies:                   0
% 2.16/1.02  inst_num_prop_implied:                  0
% 2.16/1.02  inst_num_existing_simplified:           0
% 2.16/1.02  inst_num_eq_res_simplified:             0
% 2.16/1.02  inst_num_child_elim:                    0
% 2.16/1.02  inst_num_of_dismatching_blockings:      16
% 2.16/1.02  inst_num_of_non_proper_insts:           182
% 2.16/1.02  inst_num_of_duplicates:                 0
% 2.16/1.02  inst_inst_num_from_inst_to_res:         0
% 2.16/1.02  inst_dismatching_checking_time:         0.
% 2.16/1.02  
% 2.16/1.02  ------ Resolution
% 2.16/1.02  
% 2.16/1.02  res_num_of_clauses:                     0
% 2.16/1.02  res_num_in_passive:                     0
% 2.16/1.02  res_num_in_active:                      0
% 2.16/1.02  res_num_of_loops:                       112
% 2.16/1.02  res_forward_subset_subsumed:            15
% 2.16/1.02  res_backward_subset_subsumed:           0
% 2.16/1.02  res_forward_subsumed:                   0
% 2.16/1.02  res_backward_subsumed:                  0
% 2.16/1.02  res_forward_subsumption_resolution:     0
% 2.16/1.02  res_backward_subsumption_resolution:    0
% 2.16/1.02  res_clause_to_clause_subsumption:       53
% 2.16/1.02  res_orphan_elimination:                 0
% 2.16/1.02  res_tautology_del:                      35
% 2.16/1.02  res_num_eq_res_simplified:              0
% 2.16/1.02  res_num_sel_changes:                    0
% 2.16/1.02  res_moves_from_active_to_pass:          0
% 2.16/1.02  
% 2.16/1.02  ------ Superposition
% 2.16/1.02  
% 2.16/1.02  sup_time_total:                         0.
% 2.16/1.02  sup_time_generating:                    0.
% 2.16/1.02  sup_time_sim_full:                      0.
% 2.16/1.02  sup_time_sim_immed:                     0.
% 2.16/1.02  
% 2.16/1.02  sup_num_of_clauses:                     47
% 2.16/1.02  sup_num_in_active:                      38
% 2.16/1.02  sup_num_in_passive:                     9
% 2.16/1.02  sup_num_of_loops:                       38
% 2.16/1.02  sup_fw_superposition:                   20
% 2.16/1.02  sup_bw_superposition:                   4
% 2.16/1.02  sup_immediate_simplified:               1
% 2.16/1.02  sup_given_eliminated:                   0
% 2.16/1.02  comparisons_done:                       0
% 2.16/1.02  comparisons_avoided:                    0
% 2.16/1.02  
% 2.16/1.02  ------ Simplifications
% 2.16/1.02  
% 2.16/1.02  
% 2.16/1.02  sim_fw_subset_subsumed:                 1
% 2.16/1.02  sim_bw_subset_subsumed:                 0
% 2.16/1.02  sim_fw_subsumed:                        0
% 2.16/1.02  sim_bw_subsumed:                        0
% 2.16/1.02  sim_fw_subsumption_res:                 0
% 2.16/1.02  sim_bw_subsumption_res:                 0
% 2.16/1.02  sim_tautology_del:                      6
% 2.16/1.02  sim_eq_tautology_del:                   0
% 2.16/1.02  sim_eq_res_simp:                        0
% 2.16/1.02  sim_fw_demodulated:                     0
% 2.16/1.02  sim_bw_demodulated:                     0
% 2.16/1.02  sim_light_normalised:                   5
% 2.16/1.02  sim_joinable_taut:                      0
% 2.16/1.02  sim_joinable_simp:                      0
% 2.16/1.02  sim_ac_normalised:                      0
% 2.16/1.02  sim_smt_subsumption:                    0
% 2.16/1.02  
%------------------------------------------------------------------------------
