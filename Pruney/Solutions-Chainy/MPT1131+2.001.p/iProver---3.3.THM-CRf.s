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
% DateTime   : Thu Dec  3 12:11:45 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  152 (1155 expanded)
%              Number of clauses        :   97 ( 323 expanded)
%              Number of leaves         :   13 ( 318 expanded)
%              Depth                    :   24
%              Number of atoms          :  765 (11529 expanded)
%              Number of equality atoms :  304 (1400 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

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

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f33,f32,f31,f30])).

fof(f61,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

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

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,
    ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1898,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( sK3 = sK4 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1942,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1898,c_17])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1890,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1902,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1904,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2382,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1902,c_1904])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1909,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4038,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_1909])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1903,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2375,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1902,c_1903])).

cnf(c_4463,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4038,c_2375])).

cnf(c_4464,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4463])).

cnf(c_4472,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(superposition,[status(thm)],[c_1890,c_4464])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1900,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4689,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4472,c_1900])).

cnf(c_4925,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4689])).

cnf(c_29,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_56,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_58,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_7070,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4925,c_29,c_58])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1905,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | v4_pre_topc(X3,X2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1910,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_497,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_498,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_26])).

cnf(c_503,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(renaming,[status(thm)],[c_502])).

cnf(c_1883,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v4_pre_topc(X0,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_3029,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),X0,X1,X2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),X0,X1,X2),sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1910,c_1883])).

cnf(c_3273,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
    | v4_pre_topc(X2,X1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,X2),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_3029])).

cnf(c_2153,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2154,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2153])).

cnf(c_2156,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2154])).

cnf(c_4271,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,X2),sK1) = iProver_top
    | v4_pre_topc(X2,X1) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3273,c_29,c_58,c_2156])).

cnf(c_4272,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
    | v4_pre_topc(X2,X1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,X2),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4271])).

cnf(c_7080,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
    | v4_pre_topc(X2,X1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,X2),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7070,c_4272])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1908,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10826,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v4_pre_topc(sK0(sK1,X1,X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7080,c_1908])).

cnf(c_11979,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v4_pre_topc(sK0(sK1,X1,X0),X1) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10826,c_29])).

cnf(c_11980,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
    | v5_pre_topc(X0,sK1,X1) = iProver_top
    | v4_pre_topc(sK0(sK1,X1,X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11979])).

cnf(c_11991,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1942,c_11980])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1894,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1923,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1894,c_17])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_455,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_27])).

cnf(c_456,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_26])).

cnf(c_461,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_460])).

cnf(c_1885,plain,
    ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_3674,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_1908])).

cnf(c_4185,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),sK1) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3674,c_29,c_58,c_2156])).

cnf(c_4186,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4185])).

cnf(c_7081,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7070,c_4186])).

cnf(c_8960,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7081,c_1910])).

cnf(c_8964,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | v5_pre_topc(X0,sK1,X1) != iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_8960])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1907,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v4_pre_topc(sK0(X1,X2,X0),X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7223,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7070,c_1907])).

cnf(c_7319,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7223,c_7070])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1906,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7222,plain,
    ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7070,c_1906])).

cnf(c_7334,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7222,c_7070])).

cnf(c_9855,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v5_pre_topc(X0,sK1,X1) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8964,c_29,c_58,c_2156,c_7319,c_7334])).

cnf(c_9856,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
    | v5_pre_topc(X0,sK1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9855])).

cnf(c_9868,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_9856])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1893,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1920,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1893,c_17])).

cnf(c_15,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1899,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1947,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1899,c_17])).

cnf(c_10051,plain,
    ( v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9868,c_31,c_35,c_1920,c_1947])).

cnf(c_3451,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_1906])).

cnf(c_3744,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3451,c_29,c_31,c_35,c_1920])).

cnf(c_3745,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3744])).

cnf(c_3397,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_1907])).

cnf(c_3714,plain,
    ( v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3397,c_29,c_31,c_35,c_1920])).

cnf(c_3715,plain,
    ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3714])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11991,c_10051,c_3745,c_3715,c_1923,c_1920,c_35,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.67/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.01  
% 3.67/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/1.01  
% 3.67/1.01  ------  iProver source info
% 3.67/1.01  
% 3.67/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.67/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/1.01  git: non_committed_changes: false
% 3.67/1.01  git: last_make_outside_of_git: false
% 3.67/1.01  
% 3.67/1.01  ------ 
% 3.67/1.01  
% 3.67/1.01  ------ Input Options
% 3.67/1.01  
% 3.67/1.01  --out_options                           all
% 3.67/1.01  --tptp_safe_out                         true
% 3.67/1.01  --problem_path                          ""
% 3.67/1.01  --include_path                          ""
% 3.67/1.01  --clausifier                            res/vclausify_rel
% 3.67/1.01  --clausifier_options                    --mode clausify
% 3.67/1.01  --stdin                                 false
% 3.67/1.01  --stats_out                             all
% 3.67/1.01  
% 3.67/1.01  ------ General Options
% 3.67/1.01  
% 3.67/1.01  --fof                                   false
% 3.67/1.01  --time_out_real                         305.
% 3.67/1.01  --time_out_virtual                      -1.
% 3.67/1.01  --symbol_type_check                     false
% 3.67/1.01  --clausify_out                          false
% 3.67/1.01  --sig_cnt_out                           false
% 3.67/1.01  --trig_cnt_out                          false
% 3.67/1.01  --trig_cnt_out_tolerance                1.
% 3.67/1.01  --trig_cnt_out_sk_spl                   false
% 3.67/1.01  --abstr_cl_out                          false
% 3.67/1.01  
% 3.67/1.01  ------ Global Options
% 3.67/1.01  
% 3.67/1.01  --schedule                              default
% 3.67/1.01  --add_important_lit                     false
% 3.67/1.01  --prop_solver_per_cl                    1000
% 3.67/1.01  --min_unsat_core                        false
% 3.67/1.01  --soft_assumptions                      false
% 3.67/1.01  --soft_lemma_size                       3
% 3.67/1.01  --prop_impl_unit_size                   0
% 3.67/1.01  --prop_impl_unit                        []
% 3.67/1.01  --share_sel_clauses                     true
% 3.67/1.01  --reset_solvers                         false
% 3.67/1.01  --bc_imp_inh                            [conj_cone]
% 3.67/1.01  --conj_cone_tolerance                   3.
% 3.67/1.01  --extra_neg_conj                        none
% 3.67/1.01  --large_theory_mode                     true
% 3.67/1.01  --prolific_symb_bound                   200
% 3.67/1.01  --lt_threshold                          2000
% 3.67/1.01  --clause_weak_htbl                      true
% 3.67/1.01  --gc_record_bc_elim                     false
% 3.67/1.01  
% 3.67/1.01  ------ Preprocessing Options
% 3.67/1.01  
% 3.67/1.01  --preprocessing_flag                    true
% 3.67/1.01  --time_out_prep_mult                    0.1
% 3.67/1.01  --splitting_mode                        input
% 3.67/1.01  --splitting_grd                         true
% 3.67/1.01  --splitting_cvd                         false
% 3.67/1.01  --splitting_cvd_svl                     false
% 3.67/1.01  --splitting_nvd                         32
% 3.67/1.01  --sub_typing                            true
% 3.67/1.01  --prep_gs_sim                           true
% 3.67/1.01  --prep_unflatten                        true
% 3.67/1.01  --prep_res_sim                          true
% 3.67/1.01  --prep_upred                            true
% 3.67/1.01  --prep_sem_filter                       exhaustive
% 3.67/1.01  --prep_sem_filter_out                   false
% 3.67/1.01  --pred_elim                             true
% 3.67/1.01  --res_sim_input                         true
% 3.67/1.01  --eq_ax_congr_red                       true
% 3.67/1.01  --pure_diseq_elim                       true
% 3.67/1.01  --brand_transform                       false
% 3.67/1.01  --non_eq_to_eq                          false
% 3.67/1.01  --prep_def_merge                        true
% 3.67/1.01  --prep_def_merge_prop_impl              false
% 3.67/1.01  --prep_def_merge_mbd                    true
% 3.67/1.01  --prep_def_merge_tr_red                 false
% 3.67/1.01  --prep_def_merge_tr_cl                  false
% 3.67/1.01  --smt_preprocessing                     true
% 3.67/1.01  --smt_ac_axioms                         fast
% 3.67/1.01  --preprocessed_out                      false
% 3.67/1.01  --preprocessed_stats                    false
% 3.67/1.01  
% 3.67/1.01  ------ Abstraction refinement Options
% 3.67/1.01  
% 3.67/1.01  --abstr_ref                             []
% 3.67/1.01  --abstr_ref_prep                        false
% 3.67/1.01  --abstr_ref_until_sat                   false
% 3.67/1.01  --abstr_ref_sig_restrict                funpre
% 3.67/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.67/1.01  --abstr_ref_under                       []
% 3.67/1.01  
% 3.67/1.01  ------ SAT Options
% 3.67/1.01  
% 3.67/1.01  --sat_mode                              false
% 3.67/1.01  --sat_fm_restart_options                ""
% 3.67/1.01  --sat_gr_def                            false
% 3.67/1.01  --sat_epr_types                         true
% 3.67/1.01  --sat_non_cyclic_types                  false
% 3.67/1.01  --sat_finite_models                     false
% 3.67/1.01  --sat_fm_lemmas                         false
% 3.67/1.01  --sat_fm_prep                           false
% 3.67/1.01  --sat_fm_uc_incr                        true
% 3.67/1.01  --sat_out_model                         small
% 3.67/1.01  --sat_out_clauses                       false
% 3.67/1.01  
% 3.67/1.01  ------ QBF Options
% 3.67/1.01  
% 3.67/1.01  --qbf_mode                              false
% 3.67/1.01  --qbf_elim_univ                         false
% 3.67/1.01  --qbf_dom_inst                          none
% 3.67/1.01  --qbf_dom_pre_inst                      false
% 3.67/1.01  --qbf_sk_in                             false
% 3.67/1.01  --qbf_pred_elim                         true
% 3.67/1.01  --qbf_split                             512
% 3.67/1.01  
% 3.67/1.01  ------ BMC1 Options
% 3.67/1.01  
% 3.67/1.01  --bmc1_incremental                      false
% 3.67/1.01  --bmc1_axioms                           reachable_all
% 3.67/1.01  --bmc1_min_bound                        0
% 3.67/1.01  --bmc1_max_bound                        -1
% 3.67/1.01  --bmc1_max_bound_default                -1
% 3.67/1.01  --bmc1_symbol_reachability              true
% 3.67/1.01  --bmc1_property_lemmas                  false
% 3.67/1.01  --bmc1_k_induction                      false
% 3.67/1.01  --bmc1_non_equiv_states                 false
% 3.67/1.01  --bmc1_deadlock                         false
% 3.67/1.01  --bmc1_ucm                              false
% 3.67/1.01  --bmc1_add_unsat_core                   none
% 3.67/1.01  --bmc1_unsat_core_children              false
% 3.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.67/1.01  --bmc1_out_stat                         full
% 3.67/1.01  --bmc1_ground_init                      false
% 3.67/1.01  --bmc1_pre_inst_next_state              false
% 3.67/1.01  --bmc1_pre_inst_state                   false
% 3.67/1.01  --bmc1_pre_inst_reach_state             false
% 3.67/1.01  --bmc1_out_unsat_core                   false
% 3.67/1.01  --bmc1_aig_witness_out                  false
% 3.67/1.01  --bmc1_verbose                          false
% 3.67/1.01  --bmc1_dump_clauses_tptp                false
% 3.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.67/1.01  --bmc1_dump_file                        -
% 3.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.67/1.01  --bmc1_ucm_extend_mode                  1
% 3.67/1.01  --bmc1_ucm_init_mode                    2
% 3.67/1.01  --bmc1_ucm_cone_mode                    none
% 3.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.67/1.01  --bmc1_ucm_relax_model                  4
% 3.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.67/1.01  --bmc1_ucm_layered_model                none
% 3.67/1.01  --bmc1_ucm_max_lemma_size               10
% 3.67/1.01  
% 3.67/1.01  ------ AIG Options
% 3.67/1.01  
% 3.67/1.01  --aig_mode                              false
% 3.67/1.01  
% 3.67/1.01  ------ Instantiation Options
% 3.67/1.01  
% 3.67/1.01  --instantiation_flag                    true
% 3.67/1.01  --inst_sos_flag                         false
% 3.67/1.01  --inst_sos_phase                        true
% 3.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.67/1.01  --inst_lit_sel_side                     num_symb
% 3.67/1.01  --inst_solver_per_active                1400
% 3.67/1.01  --inst_solver_calls_frac                1.
% 3.67/1.01  --inst_passive_queue_type               priority_queues
% 3.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.67/1.01  --inst_passive_queues_freq              [25;2]
% 3.67/1.01  --inst_dismatching                      true
% 3.67/1.01  --inst_eager_unprocessed_to_passive     true
% 3.67/1.01  --inst_prop_sim_given                   true
% 3.67/1.01  --inst_prop_sim_new                     false
% 3.67/1.01  --inst_subs_new                         false
% 3.97/1.01  --inst_eq_res_simp                      false
% 3.97/1.01  --inst_subs_given                       false
% 3.97/1.01  --inst_orphan_elimination               true
% 3.97/1.01  --inst_learning_loop_flag               true
% 3.97/1.01  --inst_learning_start                   3000
% 3.97/1.01  --inst_learning_factor                  2
% 3.97/1.01  --inst_start_prop_sim_after_learn       3
% 3.97/1.01  --inst_sel_renew                        solver
% 3.97/1.01  --inst_lit_activity_flag                true
% 3.97/1.01  --inst_restr_to_given                   false
% 3.97/1.01  --inst_activity_threshold               500
% 3.97/1.01  --inst_out_proof                        true
% 3.97/1.01  
% 3.97/1.01  ------ Resolution Options
% 3.97/1.01  
% 3.97/1.01  --resolution_flag                       true
% 3.97/1.01  --res_lit_sel                           adaptive
% 3.97/1.01  --res_lit_sel_side                      none
% 3.97/1.01  --res_ordering                          kbo
% 3.97/1.01  --res_to_prop_solver                    active
% 3.97/1.01  --res_prop_simpl_new                    false
% 3.97/1.01  --res_prop_simpl_given                  true
% 3.97/1.01  --res_passive_queue_type                priority_queues
% 3.97/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/1.01  --res_passive_queues_freq               [15;5]
% 3.97/1.01  --res_forward_subs                      full
% 3.97/1.01  --res_backward_subs                     full
% 3.97/1.01  --res_forward_subs_resolution           true
% 3.97/1.01  --res_backward_subs_resolution          true
% 3.97/1.01  --res_orphan_elimination                true
% 3.97/1.01  --res_time_limit                        2.
% 3.97/1.01  --res_out_proof                         true
% 3.97/1.01  
% 3.97/1.01  ------ Superposition Options
% 3.97/1.01  
% 3.97/1.01  --superposition_flag                    true
% 3.97/1.01  --sup_passive_queue_type                priority_queues
% 3.97/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.97/1.01  --demod_completeness_check              fast
% 3.97/1.01  --demod_use_ground                      true
% 3.97/1.01  --sup_to_prop_solver                    passive
% 3.97/1.01  --sup_prop_simpl_new                    true
% 3.97/1.01  --sup_prop_simpl_given                  true
% 3.97/1.01  --sup_fun_splitting                     false
% 3.97/1.01  --sup_smt_interval                      50000
% 3.97/1.01  
% 3.97/1.01  ------ Superposition Simplification Setup
% 3.97/1.01  
% 3.97/1.01  --sup_indices_passive                   []
% 3.97/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/1.01  --sup_full_bw                           [BwDemod]
% 3.97/1.01  --sup_immed_triv                        [TrivRules]
% 3.97/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/1.01  --sup_immed_bw_main                     []
% 3.97/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/1.01  
% 3.97/1.01  ------ Combination Options
% 3.97/1.01  
% 3.97/1.01  --comb_res_mult                         3
% 3.97/1.01  --comb_sup_mult                         2
% 3.97/1.01  --comb_inst_mult                        10
% 3.97/1.01  
% 3.97/1.01  ------ Debug Options
% 3.97/1.01  
% 3.97/1.01  --dbg_backtrace                         false
% 3.97/1.01  --dbg_dump_prop_clauses                 false
% 3.97/1.01  --dbg_dump_prop_clauses_file            -
% 3.97/1.01  --dbg_out_stat                          false
% 3.97/1.01  ------ Parsing...
% 3.97/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/1.01  ------ Proving...
% 3.97/1.01  ------ Problem Properties 
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  clauses                                 30
% 3.97/1.01  conjectures                             11
% 3.97/1.01  EPR                                     5
% 3.97/1.01  Horn                                    27
% 3.97/1.01  unary                                   9
% 3.97/1.01  binary                                  6
% 3.97/1.01  lits                                    84
% 3.97/1.01  lits eq                                 6
% 3.97/1.01  fd_pure                                 0
% 3.97/1.01  fd_pseudo                               0
% 3.97/1.01  fd_cond                                 0
% 3.97/1.01  fd_pseudo_cond                          2
% 3.97/1.01  AC symbols                              0
% 3.97/1.01  
% 3.97/1.01  ------ Schedule dynamic 5 is on 
% 3.97/1.01  
% 3.97/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ 
% 3.97/1.01  Current options:
% 3.97/1.01  ------ 
% 3.97/1.01  
% 3.97/1.01  ------ Input Options
% 3.97/1.01  
% 3.97/1.01  --out_options                           all
% 3.97/1.01  --tptp_safe_out                         true
% 3.97/1.01  --problem_path                          ""
% 3.97/1.01  --include_path                          ""
% 3.97/1.01  --clausifier                            res/vclausify_rel
% 3.97/1.01  --clausifier_options                    --mode clausify
% 3.97/1.01  --stdin                                 false
% 3.97/1.01  --stats_out                             all
% 3.97/1.01  
% 3.97/1.01  ------ General Options
% 3.97/1.01  
% 3.97/1.01  --fof                                   false
% 3.97/1.01  --time_out_real                         305.
% 3.97/1.01  --time_out_virtual                      -1.
% 3.97/1.01  --symbol_type_check                     false
% 3.97/1.01  --clausify_out                          false
% 3.97/1.01  --sig_cnt_out                           false
% 3.97/1.01  --trig_cnt_out                          false
% 3.97/1.01  --trig_cnt_out_tolerance                1.
% 3.97/1.01  --trig_cnt_out_sk_spl                   false
% 3.97/1.01  --abstr_cl_out                          false
% 3.97/1.01  
% 3.97/1.01  ------ Global Options
% 3.97/1.01  
% 3.97/1.01  --schedule                              default
% 3.97/1.01  --add_important_lit                     false
% 3.97/1.01  --prop_solver_per_cl                    1000
% 3.97/1.01  --min_unsat_core                        false
% 3.97/1.01  --soft_assumptions                      false
% 3.97/1.01  --soft_lemma_size                       3
% 3.97/1.01  --prop_impl_unit_size                   0
% 3.97/1.01  --prop_impl_unit                        []
% 3.97/1.01  --share_sel_clauses                     true
% 3.97/1.01  --reset_solvers                         false
% 3.97/1.01  --bc_imp_inh                            [conj_cone]
% 3.97/1.01  --conj_cone_tolerance                   3.
% 3.97/1.01  --extra_neg_conj                        none
% 3.97/1.01  --large_theory_mode                     true
% 3.97/1.01  --prolific_symb_bound                   200
% 3.97/1.01  --lt_threshold                          2000
% 3.97/1.01  --clause_weak_htbl                      true
% 3.97/1.01  --gc_record_bc_elim                     false
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing Options
% 3.97/1.01  
% 3.97/1.01  --preprocessing_flag                    true
% 3.97/1.01  --time_out_prep_mult                    0.1
% 3.97/1.01  --splitting_mode                        input
% 3.97/1.01  --splitting_grd                         true
% 3.97/1.01  --splitting_cvd                         false
% 3.97/1.01  --splitting_cvd_svl                     false
% 3.97/1.01  --splitting_nvd                         32
% 3.97/1.01  --sub_typing                            true
% 3.97/1.01  --prep_gs_sim                           true
% 3.97/1.01  --prep_unflatten                        true
% 3.97/1.01  --prep_res_sim                          true
% 3.97/1.01  --prep_upred                            true
% 3.97/1.01  --prep_sem_filter                       exhaustive
% 3.97/1.01  --prep_sem_filter_out                   false
% 3.97/1.01  --pred_elim                             true
% 3.97/1.01  --res_sim_input                         true
% 3.97/1.01  --eq_ax_congr_red                       true
% 3.97/1.01  --pure_diseq_elim                       true
% 3.97/1.01  --brand_transform                       false
% 3.97/1.01  --non_eq_to_eq                          false
% 3.97/1.01  --prep_def_merge                        true
% 3.97/1.01  --prep_def_merge_prop_impl              false
% 3.97/1.01  --prep_def_merge_mbd                    true
% 3.97/1.01  --prep_def_merge_tr_red                 false
% 3.97/1.01  --prep_def_merge_tr_cl                  false
% 3.97/1.01  --smt_preprocessing                     true
% 3.97/1.01  --smt_ac_axioms                         fast
% 3.97/1.01  --preprocessed_out                      false
% 3.97/1.01  --preprocessed_stats                    false
% 3.97/1.01  
% 3.97/1.01  ------ Abstraction refinement Options
% 3.97/1.01  
% 3.97/1.01  --abstr_ref                             []
% 3.97/1.01  --abstr_ref_prep                        false
% 3.97/1.01  --abstr_ref_until_sat                   false
% 3.97/1.01  --abstr_ref_sig_restrict                funpre
% 3.97/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/1.01  --abstr_ref_under                       []
% 3.97/1.01  
% 3.97/1.01  ------ SAT Options
% 3.97/1.01  
% 3.97/1.01  --sat_mode                              false
% 3.97/1.01  --sat_fm_restart_options                ""
% 3.97/1.01  --sat_gr_def                            false
% 3.97/1.01  --sat_epr_types                         true
% 3.97/1.01  --sat_non_cyclic_types                  false
% 3.97/1.01  --sat_finite_models                     false
% 3.97/1.01  --sat_fm_lemmas                         false
% 3.97/1.01  --sat_fm_prep                           false
% 3.97/1.01  --sat_fm_uc_incr                        true
% 3.97/1.01  --sat_out_model                         small
% 3.97/1.01  --sat_out_clauses                       false
% 3.97/1.01  
% 3.97/1.01  ------ QBF Options
% 3.97/1.01  
% 3.97/1.01  --qbf_mode                              false
% 3.97/1.01  --qbf_elim_univ                         false
% 3.97/1.01  --qbf_dom_inst                          none
% 3.97/1.01  --qbf_dom_pre_inst                      false
% 3.97/1.01  --qbf_sk_in                             false
% 3.97/1.01  --qbf_pred_elim                         true
% 3.97/1.01  --qbf_split                             512
% 3.97/1.01  
% 3.97/1.01  ------ BMC1 Options
% 3.97/1.01  
% 3.97/1.01  --bmc1_incremental                      false
% 3.97/1.01  --bmc1_axioms                           reachable_all
% 3.97/1.01  --bmc1_min_bound                        0
% 3.97/1.01  --bmc1_max_bound                        -1
% 3.97/1.01  --bmc1_max_bound_default                -1
% 3.97/1.01  --bmc1_symbol_reachability              true
% 3.97/1.01  --bmc1_property_lemmas                  false
% 3.97/1.01  --bmc1_k_induction                      false
% 3.97/1.01  --bmc1_non_equiv_states                 false
% 3.97/1.01  --bmc1_deadlock                         false
% 3.97/1.01  --bmc1_ucm                              false
% 3.97/1.01  --bmc1_add_unsat_core                   none
% 3.97/1.01  --bmc1_unsat_core_children              false
% 3.97/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/1.01  --bmc1_out_stat                         full
% 3.97/1.01  --bmc1_ground_init                      false
% 3.97/1.01  --bmc1_pre_inst_next_state              false
% 3.97/1.01  --bmc1_pre_inst_state                   false
% 3.97/1.01  --bmc1_pre_inst_reach_state             false
% 3.97/1.01  --bmc1_out_unsat_core                   false
% 3.97/1.01  --bmc1_aig_witness_out                  false
% 3.97/1.01  --bmc1_verbose                          false
% 3.97/1.01  --bmc1_dump_clauses_tptp                false
% 3.97/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.97/1.01  --bmc1_dump_file                        -
% 3.97/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.97/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.97/1.01  --bmc1_ucm_extend_mode                  1
% 3.97/1.01  --bmc1_ucm_init_mode                    2
% 3.97/1.01  --bmc1_ucm_cone_mode                    none
% 3.97/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.97/1.01  --bmc1_ucm_relax_model                  4
% 3.97/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.97/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/1.01  --bmc1_ucm_layered_model                none
% 3.97/1.01  --bmc1_ucm_max_lemma_size               10
% 3.97/1.01  
% 3.97/1.01  ------ AIG Options
% 3.97/1.01  
% 3.97/1.01  --aig_mode                              false
% 3.97/1.01  
% 3.97/1.01  ------ Instantiation Options
% 3.97/1.01  
% 3.97/1.01  --instantiation_flag                    true
% 3.97/1.01  --inst_sos_flag                         false
% 3.97/1.01  --inst_sos_phase                        true
% 3.97/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/1.01  --inst_lit_sel_side                     none
% 3.97/1.01  --inst_solver_per_active                1400
% 3.97/1.01  --inst_solver_calls_frac                1.
% 3.97/1.01  --inst_passive_queue_type               priority_queues
% 3.97/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/1.01  --inst_passive_queues_freq              [25;2]
% 3.97/1.01  --inst_dismatching                      true
% 3.97/1.01  --inst_eager_unprocessed_to_passive     true
% 3.97/1.01  --inst_prop_sim_given                   true
% 3.97/1.01  --inst_prop_sim_new                     false
% 3.97/1.01  --inst_subs_new                         false
% 3.97/1.01  --inst_eq_res_simp                      false
% 3.97/1.01  --inst_subs_given                       false
% 3.97/1.01  --inst_orphan_elimination               true
% 3.97/1.01  --inst_learning_loop_flag               true
% 3.97/1.01  --inst_learning_start                   3000
% 3.97/1.01  --inst_learning_factor                  2
% 3.97/1.01  --inst_start_prop_sim_after_learn       3
% 3.97/1.01  --inst_sel_renew                        solver
% 3.97/1.01  --inst_lit_activity_flag                true
% 3.97/1.01  --inst_restr_to_given                   false
% 3.97/1.01  --inst_activity_threshold               500
% 3.97/1.01  --inst_out_proof                        true
% 3.97/1.01  
% 3.97/1.01  ------ Resolution Options
% 3.97/1.01  
% 3.97/1.01  --resolution_flag                       false
% 3.97/1.01  --res_lit_sel                           adaptive
% 3.97/1.01  --res_lit_sel_side                      none
% 3.97/1.01  --res_ordering                          kbo
% 3.97/1.01  --res_to_prop_solver                    active
% 3.97/1.01  --res_prop_simpl_new                    false
% 3.97/1.01  --res_prop_simpl_given                  true
% 3.97/1.01  --res_passive_queue_type                priority_queues
% 3.97/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/1.01  --res_passive_queues_freq               [15;5]
% 3.97/1.01  --res_forward_subs                      full
% 3.97/1.01  --res_backward_subs                     full
% 3.97/1.01  --res_forward_subs_resolution           true
% 3.97/1.01  --res_backward_subs_resolution          true
% 3.97/1.01  --res_orphan_elimination                true
% 3.97/1.01  --res_time_limit                        2.
% 3.97/1.01  --res_out_proof                         true
% 3.97/1.01  
% 3.97/1.01  ------ Superposition Options
% 3.97/1.01  
% 3.97/1.01  --superposition_flag                    true
% 3.97/1.01  --sup_passive_queue_type                priority_queues
% 3.97/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.97/1.01  --demod_completeness_check              fast
% 3.97/1.01  --demod_use_ground                      true
% 3.97/1.01  --sup_to_prop_solver                    passive
% 3.97/1.01  --sup_prop_simpl_new                    true
% 3.97/1.01  --sup_prop_simpl_given                  true
% 3.97/1.01  --sup_fun_splitting                     false
% 3.97/1.01  --sup_smt_interval                      50000
% 3.97/1.01  
% 3.97/1.01  ------ Superposition Simplification Setup
% 3.97/1.01  
% 3.97/1.01  --sup_indices_passive                   []
% 3.97/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/1.01  --sup_full_bw                           [BwDemod]
% 3.97/1.01  --sup_immed_triv                        [TrivRules]
% 3.97/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/1.01  --sup_immed_bw_main                     []
% 3.97/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/1.01  
% 3.97/1.01  ------ Combination Options
% 3.97/1.01  
% 3.97/1.01  --comb_res_mult                         3
% 3.97/1.01  --comb_sup_mult                         2
% 3.97/1.01  --comb_inst_mult                        10
% 3.97/1.01  
% 3.97/1.01  ------ Debug Options
% 3.97/1.01  
% 3.97/1.01  --dbg_backtrace                         false
% 3.97/1.01  --dbg_dump_prop_clauses                 false
% 3.97/1.01  --dbg_dump_prop_clauses_file            -
% 3.97/1.01  --dbg_out_stat                          false
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  ------ Proving...
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  % SZS status Theorem for theBenchmark.p
% 3.97/1.01  
% 3.97/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/1.01  
% 3.97/1.01  fof(f8,conjecture,(
% 3.97/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f9,negated_conjecture,(
% 3.97/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.97/1.01    inference(negated_conjecture,[],[f8])).
% 3.97/1.01  
% 3.97/1.01  fof(f20,plain,(
% 3.97/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.97/1.01    inference(ennf_transformation,[],[f9])).
% 3.97/1.01  
% 3.97/1.01  fof(f21,plain,(
% 3.97/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.97/1.01    inference(flattening,[],[f20])).
% 3.97/1.01  
% 3.97/1.01  fof(f28,plain,(
% 3.97/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.97/1.01    inference(nnf_transformation,[],[f21])).
% 3.97/1.01  
% 3.97/1.01  fof(f29,plain,(
% 3.97/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.97/1.01    inference(flattening,[],[f28])).
% 3.97/1.01  
% 3.97/1.01  fof(f33,plain,(
% 3.97/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => ((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & sK4 = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f32,plain,(
% 3.97/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(sK3,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(sK3,X0,X1)) & sK3 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f31,plain,(
% 3.97/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) | ~v5_pre_topc(X2,X0,sK2)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) | v5_pre_topc(X2,X0,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK2)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f30,plain,(
% 3.97/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) | ~v5_pre_topc(X2,sK1,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) | v5_pre_topc(X2,sK1,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f34,plain,(
% 3.97/1.01    ((((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v5_pre_topc(sK3,sK1,sK2)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,sK1,sK2)) & sK3 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 3.97/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f33,f32,f31,f30])).
% 3.97/1.01  
% 3.97/1.01  fof(f61,plain,(
% 3.97/1.01    v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,sK1,sK2)),
% 3.97/1.01    inference(cnf_transformation,[],[f34])).
% 3.97/1.01  
% 3.97/1.01  fof(f60,plain,(
% 3.97/1.01    sK3 = sK4),
% 3.97/1.01    inference(cnf_transformation,[],[f34])).
% 3.97/1.01  
% 3.97/1.01  fof(f51,plain,(
% 3.97/1.01    l1_pre_topc(sK1)),
% 3.97/1.01    inference(cnf_transformation,[],[f34])).
% 3.97/1.01  
% 3.97/1.01  fof(f5,axiom,(
% 3.97/1.01    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f16,plain,(
% 3.97/1.01    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(ennf_transformation,[],[f5])).
% 3.97/1.01  
% 3.97/1.01  fof(f43,plain,(
% 3.97/1.01    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f16])).
% 3.97/1.01  
% 3.97/1.01  fof(f4,axiom,(
% 3.97/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f15,plain,(
% 3.97/1.01    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.97/1.01    inference(ennf_transformation,[],[f4])).
% 3.97/1.01  
% 3.97/1.01  fof(f42,plain,(
% 3.97/1.01    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f15])).
% 3.97/1.01  
% 3.97/1.01  fof(f2,axiom,(
% 3.97/1.01    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f11,plain,(
% 3.97/1.01    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(ennf_transformation,[],[f2])).
% 3.97/1.01  
% 3.97/1.01  fof(f12,plain,(
% 3.97/1.01    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(flattening,[],[f11])).
% 3.97/1.01  
% 3.97/1.01  fof(f36,plain,(
% 3.97/1.01    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f12])).
% 3.97/1.01  
% 3.97/1.01  fof(f41,plain,(
% 3.97/1.01    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f15])).
% 3.97/1.01  
% 3.97/1.01  fof(f6,axiom,(
% 3.97/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f17,plain,(
% 3.97/1.01    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.97/1.01    inference(ennf_transformation,[],[f6])).
% 3.97/1.01  
% 3.97/1.01  fof(f44,plain,(
% 3.97/1.01    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f17])).
% 3.97/1.01  
% 3.97/1.01  fof(f3,axiom,(
% 3.97/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f13,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(ennf_transformation,[],[f3])).
% 3.97/1.01  
% 3.97/1.01  fof(f14,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(flattening,[],[f13])).
% 3.97/1.01  
% 3.97/1.01  fof(f22,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(nnf_transformation,[],[f14])).
% 3.97/1.01  
% 3.97/1.01  fof(f23,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(rectify,[],[f22])).
% 3.97/1.01  
% 3.97/1.01  fof(f24,plain,(
% 3.97/1.01    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  
% 3.97/1.01  fof(f25,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) & v4_pre_topc(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.97/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 3.97/1.01  
% 3.97/1.01  fof(f37,plain,(
% 3.97/1.01    ( ! [X4,X2,X0,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f25])).
% 3.97/1.01  
% 3.97/1.01  fof(f1,axiom,(
% 3.97/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f10,plain,(
% 3.97/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.97/1.01    inference(ennf_transformation,[],[f1])).
% 3.97/1.01  
% 3.97/1.01  fof(f35,plain,(
% 3.97/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f10])).
% 3.97/1.01  
% 3.97/1.01  fof(f7,axiom,(
% 3.97/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/1.01  
% 3.97/1.01  fof(f18,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.97/1.01    inference(ennf_transformation,[],[f7])).
% 3.97/1.01  
% 3.97/1.01  fof(f19,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.97/1.01    inference(flattening,[],[f18])).
% 3.97/1.01  
% 3.97/1.01  fof(f26,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.97/1.01    inference(nnf_transformation,[],[f19])).
% 3.97/1.01  
% 3.97/1.01  fof(f27,plain,(
% 3.97/1.01    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.97/1.01    inference(flattening,[],[f26])).
% 3.97/1.01  
% 3.97/1.01  fof(f48,plain,(
% 3.97/1.01    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f27])).
% 3.97/1.01  
% 3.97/1.01  fof(f50,plain,(
% 3.97/1.01    v2_pre_topc(sK1)),
% 3.97/1.01    inference(cnf_transformation,[],[f34])).
% 3.97/1.01  
% 3.97/1.01  fof(f40,plain,(
% 3.97/1.01    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f25])).
% 3.97/1.01  
% 3.97/1.01  fof(f56,plain,(
% 3.97/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 3.97/1.01    inference(cnf_transformation,[],[f34])).
% 3.97/1.01  
% 3.97/1.01  fof(f46,plain,(
% 3.97/1.01    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f27])).
% 3.97/1.01  
% 3.97/1.01  fof(f39,plain,(
% 3.97/1.01    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | v4_pre_topc(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f25])).
% 3.97/1.01  
% 3.97/1.01  fof(f38,plain,(
% 3.97/1.01    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f25])).
% 3.97/1.01  
% 3.97/1.01  fof(f53,plain,(
% 3.97/1.01    l1_pre_topc(sK2)),
% 3.97/1.01    inference(cnf_transformation,[],[f34])).
% 3.97/1.01  
% 3.97/1.01  fof(f57,plain,(
% 3.97/1.01    v1_funct_1(sK4)),
% 3.97/1.01    inference(cnf_transformation,[],[f34])).
% 3.97/1.01  
% 3.97/1.01  fof(f55,plain,(
% 3.97/1.01    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.97/1.01    inference(cnf_transformation,[],[f34])).
% 3.97/1.01  
% 3.97/1.01  fof(f62,plain,(
% 3.97/1.01    ~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v5_pre_topc(sK3,sK1,sK2)),
% 3.97/1.01    inference(cnf_transformation,[],[f34])).
% 3.97/1.01  
% 3.97/1.01  cnf(c_16,negated_conjecture,
% 3.97/1.01      ( v5_pre_topc(sK3,sK1,sK2)
% 3.97/1.01      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
% 3.97/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1898,plain,
% 3.97/1.01      ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_17,negated_conjecture,
% 3.97/1.01      ( sK3 = sK4 ),
% 3.97/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1942,plain,
% 3.97/1.01      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 3.97/1.01      inference(light_normalisation,[status(thm)],[c_1898,c_17]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_26,negated_conjecture,
% 3.97/1.01      ( l1_pre_topc(sK1) ),
% 3.97/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1890,plain,
% 3.97/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8,plain,
% 3.97/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.97/1.01      | ~ l1_pre_topc(X0) ),
% 3.97/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1902,plain,
% 3.97/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.97/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_6,plain,
% 3.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.97/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1904,plain,
% 3.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2382,plain,
% 3.97/1.01      ( l1_pre_topc(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1902,c_1904]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1,plain,
% 3.97/1.01      ( ~ l1_pre_topc(X0)
% 3.97/1.01      | ~ v1_pre_topc(X0)
% 3.97/1.01      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.97/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1909,plain,
% 3.97/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.97/1.01      | l1_pre_topc(X0) != iProver_top
% 3.97/1.01      | v1_pre_topc(X0) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4038,plain,
% 3.97/1.01      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.97/1.01      | l1_pre_topc(X0) != iProver_top
% 3.97/1.01      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_2382,c_1909]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7,plain,
% 3.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.97/1.01      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.97/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1903,plain,
% 3.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.97/1.01      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2375,plain,
% 3.97/1.01      ( l1_pre_topc(X0) != iProver_top
% 3.97/1.01      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1902,c_1903]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4463,plain,
% 3.97/1.01      ( l1_pre_topc(X0) != iProver_top
% 3.97/1.01      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_4038,c_2375]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4464,plain,
% 3.97/1.01      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.97/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.97/1.01      inference(renaming,[status(thm)],[c_4463]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4472,plain,
% 3.97/1.01      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1890,c_4464]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10,plain,
% 3.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.97/1.01      | X2 = X1
% 3.97/1.01      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.97/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1900,plain,
% 3.97/1.01      ( X0 = X1
% 3.97/1.01      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.97/1.01      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4689,plain,
% 3.97/1.01      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 3.97/1.01      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
% 3.97/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_4472,c_1900]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4925,plain,
% 3.97/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
% 3.97/1.01      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.97/1.01      inference(equality_resolution,[status(thm)],[c_4689]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_29,plain,
% 3.97/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_56,plain,
% 3.97/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.97/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_58,plain,
% 3.97/1.01      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.97/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.97/1.01      inference(instantiation,[status(thm)],[c_56]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7070,plain,
% 3.97/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_4925,c_29,c_58]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_5,plain,
% 3.97/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.97/1.01      | ~ v5_pre_topc(X0,X1,X2)
% 3.97/1.01      | ~ v4_pre_topc(X3,X2)
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.97/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 3.97/1.01      | ~ v1_funct_1(X0)
% 3.97/1.01      | ~ l1_pre_topc(X1)
% 3.97/1.01      | ~ l1_pre_topc(X2) ),
% 3.97/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1905,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,X1,X2) != iProver_top
% 3.97/1.01      | v4_pre_topc(X3,X2) != iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.97/1.01      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(X2) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_0,plain,
% 3.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.97/1.01      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 3.97/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1910,plain,
% 3.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.97/1.01      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_12,plain,
% 3.97/1.01      ( v4_pre_topc(X0,X1)
% 3.97/1.01      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.97/1.01      | ~ v2_pre_topc(X1)
% 3.97/1.01      | ~ l1_pre_topc(X1) ),
% 3.97/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_27,negated_conjecture,
% 3.97/1.01      ( v2_pre_topc(sK1) ),
% 3.97/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_497,plain,
% 3.97/1.01      ( v4_pre_topc(X0,X1)
% 3.97/1.01      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.97/1.01      | ~ l1_pre_topc(X1)
% 3.97/1.01      | sK1 != X1 ),
% 3.97/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_498,plain,
% 3.97/1.01      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.97/1.01      | v4_pre_topc(X0,sK1)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.97/1.01      | ~ l1_pre_topc(sK1) ),
% 3.97/1.01      inference(unflattening,[status(thm)],[c_497]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_502,plain,
% 3.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
% 3.97/1.01      | v4_pre_topc(X0,sK1)
% 3.97/1.01      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_498,c_26]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_503,plain,
% 3.97/1.01      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.97/1.01      | v4_pre_topc(X0,sK1)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
% 3.97/1.01      inference(renaming,[status(thm)],[c_502]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1883,plain,
% 3.97/1.01      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.97/1.01      | v4_pre_topc(X0,sK1) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3029,plain,
% 3.97/1.01      ( v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),X0,X1,X2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),X0,X1,X2),sK1) = iProver_top
% 3.97/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),X0))) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1910,c_1883]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3273,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
% 3.97/1.01      | v4_pre_topc(X2,X1) != iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,X2),sK1) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1905,c_3029]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2153,plain,
% 3.97/1.01      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.97/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2154,plain,
% 3.97/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2153]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2156,plain,
% 3.97/1.01      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.97/1.01      inference(instantiation,[status(thm)],[c_2154]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4271,plain,
% 3.97/1.01      ( l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,X2),sK1) = iProver_top
% 3.97/1.01      | v4_pre_topc(X2,X1) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
% 3.97/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_3273,c_29,c_58,c_2156]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4272,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
% 3.97/1.01      | v4_pre_topc(X2,X1) != iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,X2),sK1) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.97/1.01      inference(renaming,[status(thm)],[c_4271]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7080,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
% 3.97/1.01      | v4_pre_topc(X2,X1) != iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,X2),sK1) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.97/1.01      inference(demodulation,[status(thm)],[c_7070,c_4272]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_2,plain,
% 3.97/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.97/1.01      | v5_pre_topc(X0,X1,X2)
% 3.97/1.01      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.97/1.01      | ~ v1_funct_1(X0)
% 3.97/1.01      | ~ l1_pre_topc(X1)
% 3.97/1.01      | ~ l1_pre_topc(X2) ),
% 3.97/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1908,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,X1,X2) = iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(X2) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10826,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 3.97/1.01      | v4_pre_topc(sK0(sK1,X1,X0),X1) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_7080,c_1908]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_11979,plain,
% 3.97/1.01      ( l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | v4_pre_topc(sK0(sK1,X1,X0),X1) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
% 3.97/1.01      | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_10826,c_29]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_11980,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,sK1,X1) = iProver_top
% 3.97/1.01      | v4_pre_topc(sK0(sK1,X1,X0),X1) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(sK0(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.97/1.01      inference(renaming,[status(thm)],[c_11979]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_11991,plain,
% 3.97/1.01      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 3.97/1.01      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) != iProver_top
% 3.97/1.01      | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.97/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 3.97/1.01      | v1_funct_1(sK4) != iProver_top
% 3.97/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1942,c_11980]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_21,negated_conjecture,
% 3.97/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 3.97/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1894,plain,
% 3.97/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1923,plain,
% 3.97/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.97/1.01      inference(light_normalisation,[status(thm)],[c_1894,c_17]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_14,plain,
% 3.97/1.01      ( ~ v4_pre_topc(X0,X1)
% 3.97/1.01      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/1.01      | ~ v2_pre_topc(X1)
% 3.97/1.01      | ~ l1_pre_topc(X1) ),
% 3.97/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_455,plain,
% 3.97/1.01      ( ~ v4_pre_topc(X0,X1)
% 3.97/1.01      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.97/1.01      | ~ l1_pre_topc(X1)
% 3.97/1.01      | sK1 != X1 ),
% 3.97/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_27]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_456,plain,
% 3.97/1.01      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.97/1.01      | ~ v4_pre_topc(X0,sK1)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.97/1.01      | ~ l1_pre_topc(sK1) ),
% 3.97/1.01      inference(unflattening,[status(thm)],[c_455]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_460,plain,
% 3.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.97/1.01      | ~ v4_pre_topc(X0,sK1)
% 3.97/1.01      | v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_456,c_26]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_461,plain,
% 3.97/1.01      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.97/1.01      | ~ v4_pre_topc(X0,sK1)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.97/1.01      inference(renaming,[status(thm)],[c_460]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1885,plain,
% 3.97/1.01      ( v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.97/1.01      | v4_pre_topc(X0,sK1) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3674,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),sK1) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1885,c_1908]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4185,plain,
% 3.97/1.01      ( l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),sK1) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_3674,c_29,c_58,c_2156]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4186,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),sK1) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.97/1.01      inference(renaming,[status(thm)],[c_4185]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7081,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),sK1) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.97/1.01      inference(demodulation,[status(thm)],[c_7070,c_4186]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8960,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0)),sK1) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.97/1.01      inference(forward_subsumption_resolution,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_7081,c_1910]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_8964,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | v5_pre_topc(X0,sK1,X1) != iProver_top
% 3.97/1.01      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),X1) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1905,c_8960]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3,plain,
% 3.97/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.97/1.01      | v5_pre_topc(X0,X1,X2)
% 3.97/1.01      | v4_pre_topc(sK0(X1,X2,X0),X2)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.97/1.01      | ~ v1_funct_1(X0)
% 3.97/1.01      | ~ l1_pre_topc(X1)
% 3.97/1.01      | ~ l1_pre_topc(X2) ),
% 3.97/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1907,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,X1,X2) = iProver_top
% 3.97/1.01      | v4_pre_topc(sK0(X1,X2,X0),X2) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(X2) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7223,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),X1) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_7070,c_1907]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7319,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | v4_pre_topc(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),X1) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.97/1.01      inference(light_normalisation,[status(thm)],[c_7223,c_7070]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_4,plain,
% 3.97/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.97/1.01      | v5_pre_topc(X0,X1,X2)
% 3.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.97/1.01      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 3.97/1.01      | ~ v1_funct_1(X0)
% 3.97/1.01      | ~ l1_pre_topc(X1)
% 3.97/1.01      | ~ l1_pre_topc(X2) ),
% 3.97/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1906,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,X1,X2) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.97/1.01      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(X2) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7222,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_7070,c_1906]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_7334,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | m1_subset_1(sK0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.97/1.01      inference(light_normalisation,[status(thm)],[c_7222,c_7070]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9855,plain,
% 3.97/1.01      ( l1_pre_topc(X1) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,sK1,X1) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_8964,c_29,c_58,c_2156,c_7319,c_7334]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9856,plain,
% 3.97/1.01      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1)) != iProver_top
% 3.97/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1) = iProver_top
% 3.97/1.01      | v5_pre_topc(X0,sK1,X1) != iProver_top
% 3.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) != iProver_top
% 3.97/1.01      | v1_funct_1(X0) != iProver_top
% 3.97/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.97/1.01      inference(renaming,[status(thm)],[c_9855]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_9868,plain,
% 3.97/1.01      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,sK1,sK2) != iProver_top
% 3.97/1.01      | v1_funct_1(sK4) != iProver_top
% 3.97/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1923,c_9856]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_24,negated_conjecture,
% 3.97/1.01      ( l1_pre_topc(sK2) ),
% 3.97/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_31,plain,
% 3.97/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_20,negated_conjecture,
% 3.97/1.01      ( v1_funct_1(sK4) ),
% 3.97/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_35,plain,
% 3.97/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_22,negated_conjecture,
% 3.97/1.01      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 3.97/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1893,plain,
% 3.97/1.01      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1920,plain,
% 3.97/1.01      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 3.97/1.01      inference(light_normalisation,[status(thm)],[c_1893,c_17]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_15,negated_conjecture,
% 3.97/1.01      ( ~ v5_pre_topc(sK3,sK1,sK2)
% 3.97/1.01      | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
% 3.97/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1899,plain,
% 3.97/1.01      ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top ),
% 3.97/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_1947,plain,
% 3.97/1.01      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
% 3.97/1.01      inference(light_normalisation,[status(thm)],[c_1899,c_17]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_10051,plain,
% 3.97/1.01      ( v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_9868,c_31,c_35,c_1920,c_1947]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3451,plain,
% 3.97/1.01      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 3.97/1.01      | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.97/1.01      | v1_funct_1(sK4) != iProver_top
% 3.97/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.97/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1923,c_1906]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3744,plain,
% 3.97/1.01      ( m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_3451,c_29,c_31,c_35,c_1920]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3745,plain,
% 3.97/1.01      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 3.97/1.01      | m1_subset_1(sK0(sK1,sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.97/1.01      inference(renaming,[status(thm)],[c_3744]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3397,plain,
% 3.97/1.01      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 3.97/1.01      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
% 3.97/1.01      | v1_funct_1(sK4) != iProver_top
% 3.97/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.97/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.97/1.01      inference(superposition,[status(thm)],[c_1923,c_1907]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3714,plain,
% 3.97/1.01      ( v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top
% 3.97/1.01      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 3.97/1.01      inference(global_propositional_subsumption,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_3397,c_29,c_31,c_35,c_1920]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(c_3715,plain,
% 3.97/1.01      ( v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 3.97/1.01      | v4_pre_topc(sK0(sK1,sK2,sK4),sK2) = iProver_top ),
% 3.97/1.01      inference(renaming,[status(thm)],[c_3714]) ).
% 3.97/1.01  
% 3.97/1.01  cnf(contradiction,plain,
% 3.97/1.01      ( $false ),
% 3.97/1.01      inference(minisat,
% 3.97/1.01                [status(thm)],
% 3.97/1.01                [c_11991,c_10051,c_3745,c_3715,c_1923,c_1920,c_35,c_31]) ).
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/1.01  
% 3.97/1.01  ------                               Statistics
% 3.97/1.01  
% 3.97/1.01  ------ General
% 3.97/1.01  
% 3.97/1.01  abstr_ref_over_cycles:                  0
% 3.97/1.01  abstr_ref_under_cycles:                 0
% 3.97/1.01  gc_basic_clause_elim:                   0
% 3.97/1.01  forced_gc_time:                         0
% 3.97/1.01  parsing_time:                           0.01
% 3.97/1.01  unif_index_cands_time:                  0.
% 3.97/1.01  unif_index_add_time:                    0.
% 3.97/1.01  orderings_time:                         0.
% 3.97/1.01  out_proof_time:                         0.029
% 3.97/1.01  total_time:                             0.442
% 3.97/1.01  num_of_symbols:                         50
% 3.97/1.01  num_of_terms:                           11775
% 3.97/1.01  
% 3.97/1.01  ------ Preprocessing
% 3.97/1.01  
% 3.97/1.01  num_of_splits:                          0
% 3.97/1.01  num_of_split_atoms:                     0
% 3.97/1.01  num_of_reused_defs:                     0
% 3.97/1.01  num_eq_ax_congr_red:                    8
% 3.97/1.01  num_of_sem_filtered_clauses:            1
% 3.97/1.01  num_of_subtypes:                        0
% 3.97/1.01  monotx_restored_types:                  0
% 3.97/1.01  sat_num_of_epr_types:                   0
% 3.97/1.01  sat_num_of_non_cyclic_types:            0
% 3.97/1.01  sat_guarded_non_collapsed_types:        0
% 3.97/1.01  num_pure_diseq_elim:                    0
% 3.97/1.01  simp_replaced_by:                       0
% 3.97/1.01  res_preprocessed:                       119
% 3.97/1.01  prep_upred:                             0
% 3.97/1.01  prep_unflattend:                        25
% 3.97/1.01  smt_new_axioms:                         0
% 3.97/1.01  pred_elim_cands:                        8
% 3.97/1.01  pred_elim:                              1
% 3.97/1.01  pred_elim_cl:                           -2
% 3.97/1.01  pred_elim_cycles:                       4
% 3.97/1.01  merged_defs:                            6
% 3.97/1.01  merged_defs_ncl:                        0
% 3.97/1.01  bin_hyper_res:                          6
% 3.97/1.01  prep_cycles:                            3
% 3.97/1.01  pred_elim_time:                         0.019
% 3.97/1.01  splitting_time:                         0.
% 3.97/1.01  sem_filter_time:                        0.
% 3.97/1.01  monotx_time:                            0.001
% 3.97/1.01  subtype_inf_time:                       0.
% 3.97/1.01  
% 3.97/1.01  ------ Problem properties
% 3.97/1.01  
% 3.97/1.01  clauses:                                30
% 3.97/1.01  conjectures:                            11
% 3.97/1.01  epr:                                    5
% 3.97/1.01  horn:                                   27
% 3.97/1.01  ground:                                 11
% 3.97/1.01  unary:                                  9
% 3.97/1.01  binary:                                 6
% 3.97/1.01  lits:                                   84
% 3.97/1.01  lits_eq:                                6
% 3.97/1.01  fd_pure:                                0
% 3.97/1.01  fd_pseudo:                              0
% 3.97/1.01  fd_cond:                                0
% 3.97/1.01  fd_pseudo_cond:                         2
% 3.97/1.01  ac_symbols:                             0
% 3.97/1.01  
% 3.97/1.01  ------ Propositional Solver
% 3.97/1.01  
% 3.97/1.01  prop_solver_calls:                      26
% 3.97/1.01  prop_fast_solver_calls:                 1701
% 3.97/1.01  smt_solver_calls:                       0
% 3.97/1.01  smt_fast_solver_calls:                  0
% 3.97/1.01  prop_num_of_clauses:                    3476
% 3.97/1.01  prop_preprocess_simplified:             7825
% 3.97/1.01  prop_fo_subsumed:                       89
% 3.97/1.01  prop_solver_time:                       0.
% 3.97/1.01  smt_solver_time:                        0.
% 3.97/1.01  smt_fast_solver_time:                   0.
% 3.97/1.01  prop_fast_solver_time:                  0.
% 3.97/1.01  prop_unsat_core_time:                   0.
% 3.97/1.01  
% 3.97/1.01  ------ QBF
% 3.97/1.01  
% 3.97/1.01  qbf_q_res:                              0
% 3.97/1.01  qbf_num_tautologies:                    0
% 3.97/1.01  qbf_prep_cycles:                        0
% 3.97/1.01  
% 3.97/1.01  ------ BMC1
% 3.97/1.01  
% 3.97/1.01  bmc1_current_bound:                     -1
% 3.97/1.01  bmc1_last_solved_bound:                 -1
% 3.97/1.01  bmc1_unsat_core_size:                   -1
% 3.97/1.01  bmc1_unsat_core_parents_size:           -1
% 3.97/1.01  bmc1_merge_next_fun:                    0
% 3.97/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.97/1.01  
% 3.97/1.01  ------ Instantiation
% 3.97/1.01  
% 3.97/1.01  inst_num_of_clauses:                    969
% 3.97/1.01  inst_num_in_passive:                    112
% 3.97/1.01  inst_num_in_active:                     648
% 3.97/1.01  inst_num_in_unprocessed:                209
% 3.97/1.01  inst_num_of_loops:                      680
% 3.97/1.01  inst_num_of_learning_restarts:          0
% 3.97/1.01  inst_num_moves_active_passive:          28
% 3.97/1.01  inst_lit_activity:                      0
% 3.97/1.01  inst_lit_activity_moves:                0
% 3.97/1.01  inst_num_tautologies:                   0
% 3.97/1.01  inst_num_prop_implied:                  0
% 3.97/1.01  inst_num_existing_simplified:           0
% 3.97/1.01  inst_num_eq_res_simplified:             0
% 3.97/1.01  inst_num_child_elim:                    0
% 3.97/1.01  inst_num_of_dismatching_blockings:      980
% 3.97/1.01  inst_num_of_non_proper_insts:           1905
% 3.97/1.01  inst_num_of_duplicates:                 0
% 3.97/1.01  inst_inst_num_from_inst_to_res:         0
% 3.97/1.01  inst_dismatching_checking_time:         0.
% 3.97/1.01  
% 3.97/1.01  ------ Resolution
% 3.97/1.01  
% 3.97/1.01  res_num_of_clauses:                     0
% 3.97/1.01  res_num_in_passive:                     0
% 3.97/1.01  res_num_in_active:                      0
% 3.97/1.01  res_num_of_loops:                       122
% 3.97/1.01  res_forward_subset_subsumed:            269
% 3.97/1.01  res_backward_subset_subsumed:           2
% 3.97/1.01  res_forward_subsumed:                   0
% 3.97/1.01  res_backward_subsumed:                  0
% 3.97/1.01  res_forward_subsumption_resolution:     0
% 3.97/1.01  res_backward_subsumption_resolution:    0
% 3.97/1.01  res_clause_to_clause_subsumption:       657
% 3.97/1.01  res_orphan_elimination:                 0
% 3.97/1.01  res_tautology_del:                      214
% 3.97/1.01  res_num_eq_res_simplified:              0
% 3.97/1.01  res_num_sel_changes:                    0
% 3.97/1.01  res_moves_from_active_to_pass:          0
% 3.97/1.01  
% 3.97/1.01  ------ Superposition
% 3.97/1.01  
% 3.97/1.01  sup_time_total:                         0.
% 3.97/1.01  sup_time_generating:                    0.
% 3.97/1.01  sup_time_sim_full:                      0.
% 3.97/1.01  sup_time_sim_immed:                     0.
% 3.97/1.01  
% 3.97/1.01  sup_num_of_clauses:                     192
% 3.97/1.01  sup_num_in_active:                      99
% 3.97/1.01  sup_num_in_passive:                     93
% 3.97/1.01  sup_num_of_loops:                       134
% 3.97/1.01  sup_fw_superposition:                   137
% 3.97/1.01  sup_bw_superposition:                   113
% 3.97/1.01  sup_immediate_simplified:               95
% 3.97/1.01  sup_given_eliminated:                   0
% 3.97/1.01  comparisons_done:                       0
% 3.97/1.01  comparisons_avoided:                    0
% 3.97/1.01  
% 3.97/1.01  ------ Simplifications
% 3.97/1.01  
% 3.97/1.01  
% 3.97/1.01  sim_fw_subset_subsumed:                 3
% 3.97/1.01  sim_bw_subset_subsumed:                 13
% 3.97/1.01  sim_fw_subsumed:                        10
% 3.97/1.01  sim_bw_subsumed:                        0
% 3.97/1.01  sim_fw_subsumption_res:                 3
% 3.97/1.01  sim_bw_subsumption_res:                 0
% 3.97/1.01  sim_tautology_del:                      37
% 3.97/1.01  sim_eq_tautology_del:                   24
% 3.97/1.01  sim_eq_res_simp:                        0
% 3.97/1.01  sim_fw_demodulated:                     2
% 3.97/1.01  sim_bw_demodulated:                     36
% 3.97/1.01  sim_light_normalised:                   95
% 3.97/1.01  sim_joinable_taut:                      0
% 3.97/1.01  sim_joinable_simp:                      0
% 3.97/1.01  sim_ac_normalised:                      0
% 3.97/1.01  sim_smt_subsumption:                    0
% 3.97/1.01  
%------------------------------------------------------------------------------
