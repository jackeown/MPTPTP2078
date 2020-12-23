%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:47 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  146 (1768 expanded)
%              Number of clauses        :   89 ( 586 expanded)
%              Number of leaves         :   12 ( 440 expanded)
%              Depth                    :   18
%              Number of atoms          :  758 (14364 expanded)
%              Number of equality atoms :  251 (1984 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   3 average)
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f30,plain,(
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
     => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK3 = X2
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
              | ~ v5_pre_topc(sK2,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK2,X0,X1) )
            & sK2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                  | ~ v5_pre_topc(X2,X0,sK1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                  | v5_pre_topc(X2,X0,sK1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f30,f29,f28,f27])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
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
    inference(equality_resolution,[],[f41])).

fof(f55,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
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
    inference(equality_resolution,[],[f43])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
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
    inference(equality_resolution,[],[f40])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
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
    inference(equality_resolution,[],[f42])).

fof(f56,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1345,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1362,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1364,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1841,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1362,c_1364])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1365,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2099,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_1365])).

cnf(c_1615,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1616,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1615])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1834,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1362,c_1363])).

cnf(c_2485,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2099,c_1616,c_1834,c_1841])).

cnf(c_2486,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2485])).

cnf(c_2493,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(superposition,[status(thm)],[c_1345,c_2486])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1358,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2603,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2493,c_1358])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1586,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2080,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_2081,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2080])).

cnf(c_2375,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2376,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2375])).

cnf(c_2386,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2391,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2386])).

cnf(c_2604,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2493,c_1358])).

cnf(c_3110,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2603,c_28,c_2081,c_2376,c_2391,c_2604])).

cnf(c_3111,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0 ),
    inference(renaming,[status(thm)],[c_3110])).

cnf(c_3117,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
    inference(equality_resolution,[status(thm)],[c_3111])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1351,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3705,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3117,c_1351])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1357,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4155,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3705,c_1357])).

cnf(c_13,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1352,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1419,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1352,c_14])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1355,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2882,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_1355])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_25,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_27,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_33,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_56,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_58,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_59,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_61,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_1587,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1586])).

cnf(c_1589,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_3218,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2882,c_25,c_26,c_27,c_28,c_32,c_33,c_58,c_61,c_1589])).

cnf(c_3219,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3218])).

cnf(c_3226,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_3219])).

cnf(c_4157,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3705,c_3226])).

cnf(c_4201,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4155,c_4157])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1356,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4156,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3705,c_1356])).

cnf(c_4181,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4156,c_4157])).

cnf(c_1350,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3706,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3117,c_1350])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1354,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2364,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_1354])).

cnf(c_2476,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2364,c_25,c_26,c_27,c_28,c_32,c_33,c_58,c_61,c_1589])).

cnf(c_2477,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2476])).

cnf(c_12,negated_conjecture,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1353,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1436,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1353,c_14])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1347,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1379,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1347,c_14])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1348,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1382,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1348,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4201,c_4181,c_3706,c_3705,c_2477,c_1436,c_1379,c_1382,c_32,c_28,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.13/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.13/0.99  
% 2.13/0.99  ------  iProver source info
% 2.13/0.99  
% 2.13/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.13/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.13/0.99  git: non_committed_changes: false
% 2.13/0.99  git: last_make_outside_of_git: false
% 2.13/0.99  
% 2.13/0.99  ------ 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options
% 2.13/0.99  
% 2.13/0.99  --out_options                           all
% 2.13/0.99  --tptp_safe_out                         true
% 2.13/0.99  --problem_path                          ""
% 2.13/0.99  --include_path                          ""
% 2.13/0.99  --clausifier                            res/vclausify_rel
% 2.13/0.99  --clausifier_options                    --mode clausify
% 2.13/0.99  --stdin                                 false
% 2.13/0.99  --stats_out                             all
% 2.13/0.99  
% 2.13/0.99  ------ General Options
% 2.13/0.99  
% 2.13/0.99  --fof                                   false
% 2.13/0.99  --time_out_real                         305.
% 2.13/0.99  --time_out_virtual                      -1.
% 2.13/0.99  --symbol_type_check                     false
% 2.13/0.99  --clausify_out                          false
% 2.13/0.99  --sig_cnt_out                           false
% 2.13/0.99  --trig_cnt_out                          false
% 2.13/0.99  --trig_cnt_out_tolerance                1.
% 2.13/0.99  --trig_cnt_out_sk_spl                   false
% 2.13/0.99  --abstr_cl_out                          false
% 2.13/0.99  
% 2.13/0.99  ------ Global Options
% 2.13/0.99  
% 2.13/0.99  --schedule                              default
% 2.13/0.99  --add_important_lit                     false
% 2.13/0.99  --prop_solver_per_cl                    1000
% 2.13/0.99  --min_unsat_core                        false
% 2.13/0.99  --soft_assumptions                      false
% 2.13/0.99  --soft_lemma_size                       3
% 2.13/0.99  --prop_impl_unit_size                   0
% 2.13/0.99  --prop_impl_unit                        []
% 2.13/0.99  --share_sel_clauses                     true
% 2.13/0.99  --reset_solvers                         false
% 2.13/0.99  --bc_imp_inh                            [conj_cone]
% 2.13/0.99  --conj_cone_tolerance                   3.
% 2.13/0.99  --extra_neg_conj                        none
% 2.13/0.99  --large_theory_mode                     true
% 2.13/0.99  --prolific_symb_bound                   200
% 2.13/0.99  --lt_threshold                          2000
% 2.13/0.99  --clause_weak_htbl                      true
% 2.13/0.99  --gc_record_bc_elim                     false
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing Options
% 2.13/0.99  
% 2.13/0.99  --preprocessing_flag                    true
% 2.13/0.99  --time_out_prep_mult                    0.1
% 2.13/0.99  --splitting_mode                        input
% 2.13/0.99  --splitting_grd                         true
% 2.13/0.99  --splitting_cvd                         false
% 2.13/0.99  --splitting_cvd_svl                     false
% 2.13/0.99  --splitting_nvd                         32
% 2.13/0.99  --sub_typing                            true
% 2.13/0.99  --prep_gs_sim                           true
% 2.13/0.99  --prep_unflatten                        true
% 2.13/0.99  --prep_res_sim                          true
% 2.13/0.99  --prep_upred                            true
% 2.13/0.99  --prep_sem_filter                       exhaustive
% 2.13/0.99  --prep_sem_filter_out                   false
% 2.13/0.99  --pred_elim                             true
% 2.13/0.99  --res_sim_input                         true
% 2.13/0.99  --eq_ax_congr_red                       true
% 2.13/0.99  --pure_diseq_elim                       true
% 2.13/0.99  --brand_transform                       false
% 2.13/0.99  --non_eq_to_eq                          false
% 2.13/0.99  --prep_def_merge                        true
% 2.13/0.99  --prep_def_merge_prop_impl              false
% 2.13/0.99  --prep_def_merge_mbd                    true
% 2.13/0.99  --prep_def_merge_tr_red                 false
% 2.13/0.99  --prep_def_merge_tr_cl                  false
% 2.13/0.99  --smt_preprocessing                     true
% 2.13/0.99  --smt_ac_axioms                         fast
% 2.13/0.99  --preprocessed_out                      false
% 2.13/0.99  --preprocessed_stats                    false
% 2.13/0.99  
% 2.13/0.99  ------ Abstraction refinement Options
% 2.13/0.99  
% 2.13/0.99  --abstr_ref                             []
% 2.13/0.99  --abstr_ref_prep                        false
% 2.13/0.99  --abstr_ref_until_sat                   false
% 2.13/0.99  --abstr_ref_sig_restrict                funpre
% 2.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.99  --abstr_ref_under                       []
% 2.13/0.99  
% 2.13/0.99  ------ SAT Options
% 2.13/0.99  
% 2.13/0.99  --sat_mode                              false
% 2.13/0.99  --sat_fm_restart_options                ""
% 2.13/0.99  --sat_gr_def                            false
% 2.13/0.99  --sat_epr_types                         true
% 2.13/0.99  --sat_non_cyclic_types                  false
% 2.13/0.99  --sat_finite_models                     false
% 2.13/0.99  --sat_fm_lemmas                         false
% 2.13/0.99  --sat_fm_prep                           false
% 2.13/0.99  --sat_fm_uc_incr                        true
% 2.13/0.99  --sat_out_model                         small
% 2.13/0.99  --sat_out_clauses                       false
% 2.13/0.99  
% 2.13/0.99  ------ QBF Options
% 2.13/0.99  
% 2.13/0.99  --qbf_mode                              false
% 2.13/0.99  --qbf_elim_univ                         false
% 2.13/0.99  --qbf_dom_inst                          none
% 2.13/0.99  --qbf_dom_pre_inst                      false
% 2.13/0.99  --qbf_sk_in                             false
% 2.13/0.99  --qbf_pred_elim                         true
% 2.13/0.99  --qbf_split                             512
% 2.13/0.99  
% 2.13/0.99  ------ BMC1 Options
% 2.13/0.99  
% 2.13/0.99  --bmc1_incremental                      false
% 2.13/0.99  --bmc1_axioms                           reachable_all
% 2.13/0.99  --bmc1_min_bound                        0
% 2.13/0.99  --bmc1_max_bound                        -1
% 2.13/0.99  --bmc1_max_bound_default                -1
% 2.13/0.99  --bmc1_symbol_reachability              true
% 2.13/0.99  --bmc1_property_lemmas                  false
% 2.13/0.99  --bmc1_k_induction                      false
% 2.13/0.99  --bmc1_non_equiv_states                 false
% 2.13/0.99  --bmc1_deadlock                         false
% 2.13/0.99  --bmc1_ucm                              false
% 2.13/0.99  --bmc1_add_unsat_core                   none
% 2.13/0.99  --bmc1_unsat_core_children              false
% 2.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/0.99  --bmc1_out_stat                         full
% 2.13/0.99  --bmc1_ground_init                      false
% 2.13/0.99  --bmc1_pre_inst_next_state              false
% 2.13/0.99  --bmc1_pre_inst_state                   false
% 2.13/0.99  --bmc1_pre_inst_reach_state             false
% 2.13/0.99  --bmc1_out_unsat_core                   false
% 2.13/0.99  --bmc1_aig_witness_out                  false
% 2.13/0.99  --bmc1_verbose                          false
% 2.13/0.99  --bmc1_dump_clauses_tptp                false
% 2.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.13/0.99  --bmc1_dump_file                        -
% 2.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.13/0.99  --bmc1_ucm_extend_mode                  1
% 2.13/0.99  --bmc1_ucm_init_mode                    2
% 2.13/0.99  --bmc1_ucm_cone_mode                    none
% 2.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.13/0.99  --bmc1_ucm_relax_model                  4
% 2.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/0.99  --bmc1_ucm_layered_model                none
% 2.13/0.99  --bmc1_ucm_max_lemma_size               10
% 2.13/0.99  
% 2.13/0.99  ------ AIG Options
% 2.13/0.99  
% 2.13/0.99  --aig_mode                              false
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation Options
% 2.13/0.99  
% 2.13/0.99  --instantiation_flag                    true
% 2.13/0.99  --inst_sos_flag                         false
% 2.13/0.99  --inst_sos_phase                        true
% 2.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel_side                     num_symb
% 2.13/0.99  --inst_solver_per_active                1400
% 2.13/0.99  --inst_solver_calls_frac                1.
% 2.13/0.99  --inst_passive_queue_type               priority_queues
% 2.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/0.99  --inst_passive_queues_freq              [25;2]
% 2.13/0.99  --inst_dismatching                      true
% 2.13/0.99  --inst_eager_unprocessed_to_passive     true
% 2.13/0.99  --inst_prop_sim_given                   true
% 2.13/0.99  --inst_prop_sim_new                     false
% 2.13/0.99  --inst_subs_new                         false
% 2.13/0.99  --inst_eq_res_simp                      false
% 2.13/0.99  --inst_subs_given                       false
% 2.13/0.99  --inst_orphan_elimination               true
% 2.13/0.99  --inst_learning_loop_flag               true
% 2.13/0.99  --inst_learning_start                   3000
% 2.13/0.99  --inst_learning_factor                  2
% 2.13/0.99  --inst_start_prop_sim_after_learn       3
% 2.13/0.99  --inst_sel_renew                        solver
% 2.13/0.99  --inst_lit_activity_flag                true
% 2.13/0.99  --inst_restr_to_given                   false
% 2.13/0.99  --inst_activity_threshold               500
% 2.13/0.99  --inst_out_proof                        true
% 2.13/0.99  
% 2.13/0.99  ------ Resolution Options
% 2.13/0.99  
% 2.13/0.99  --resolution_flag                       true
% 2.13/0.99  --res_lit_sel                           adaptive
% 2.13/0.99  --res_lit_sel_side                      none
% 2.13/0.99  --res_ordering                          kbo
% 2.13/0.99  --res_to_prop_solver                    active
% 2.13/0.99  --res_prop_simpl_new                    false
% 2.13/0.99  --res_prop_simpl_given                  true
% 2.13/0.99  --res_passive_queue_type                priority_queues
% 2.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/0.99  --res_passive_queues_freq               [15;5]
% 2.13/0.99  --res_forward_subs                      full
% 2.13/0.99  --res_backward_subs                     full
% 2.13/0.99  --res_forward_subs_resolution           true
% 2.13/0.99  --res_backward_subs_resolution          true
% 2.13/0.99  --res_orphan_elimination                true
% 2.13/0.99  --res_time_limit                        2.
% 2.13/0.99  --res_out_proof                         true
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Options
% 2.13/0.99  
% 2.13/0.99  --superposition_flag                    true
% 2.13/0.99  --sup_passive_queue_type                priority_queues
% 2.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.13/0.99  --demod_completeness_check              fast
% 2.13/0.99  --demod_use_ground                      true
% 2.13/0.99  --sup_to_prop_solver                    passive
% 2.13/0.99  --sup_prop_simpl_new                    true
% 2.13/0.99  --sup_prop_simpl_given                  true
% 2.13/0.99  --sup_fun_splitting                     false
% 2.13/0.99  --sup_smt_interval                      50000
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Simplification Setup
% 2.13/0.99  
% 2.13/0.99  --sup_indices_passive                   []
% 2.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_full_bw                           [BwDemod]
% 2.13/0.99  --sup_immed_triv                        [TrivRules]
% 2.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_immed_bw_main                     []
% 2.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  
% 2.13/0.99  ------ Combination Options
% 2.13/0.99  
% 2.13/0.99  --comb_res_mult                         3
% 2.13/0.99  --comb_sup_mult                         2
% 2.13/0.99  --comb_inst_mult                        10
% 2.13/0.99  
% 2.13/0.99  ------ Debug Options
% 2.13/0.99  
% 2.13/0.99  --dbg_backtrace                         false
% 2.13/0.99  --dbg_dump_prop_clauses                 false
% 2.13/0.99  --dbg_dump_prop_clauses_file            -
% 2.13/0.99  --dbg_out_stat                          false
% 2.13/0.99  ------ Parsing...
% 2.13/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.13/0.99  ------ Proving...
% 2.13/0.99  ------ Problem Properties 
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  clauses                                 25
% 2.13/0.99  conjectures                             13
% 2.13/0.99  EPR                                     7
% 2.13/0.99  Horn                                    24
% 2.13/0.99  unary                                   11
% 2.13/0.99  binary                                  5
% 2.13/0.99  lits                                    80
% 2.13/0.99  lits eq                                 6
% 2.13/0.99  fd_pure                                 0
% 2.13/0.99  fd_pseudo                               0
% 2.13/0.99  fd_cond                                 0
% 2.13/0.99  fd_pseudo_cond                          2
% 2.13/0.99  AC symbols                              0
% 2.13/0.99  
% 2.13/0.99  ------ Schedule dynamic 5 is on 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  ------ 
% 2.13/0.99  Current options:
% 2.13/0.99  ------ 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options
% 2.13/0.99  
% 2.13/0.99  --out_options                           all
% 2.13/0.99  --tptp_safe_out                         true
% 2.13/0.99  --problem_path                          ""
% 2.13/0.99  --include_path                          ""
% 2.13/0.99  --clausifier                            res/vclausify_rel
% 2.13/0.99  --clausifier_options                    --mode clausify
% 2.13/0.99  --stdin                                 false
% 2.13/0.99  --stats_out                             all
% 2.13/0.99  
% 2.13/0.99  ------ General Options
% 2.13/0.99  
% 2.13/0.99  --fof                                   false
% 2.13/0.99  --time_out_real                         305.
% 2.13/0.99  --time_out_virtual                      -1.
% 2.13/0.99  --symbol_type_check                     false
% 2.13/0.99  --clausify_out                          false
% 2.13/0.99  --sig_cnt_out                           false
% 2.13/0.99  --trig_cnt_out                          false
% 2.13/0.99  --trig_cnt_out_tolerance                1.
% 2.13/0.99  --trig_cnt_out_sk_spl                   false
% 2.13/0.99  --abstr_cl_out                          false
% 2.13/0.99  
% 2.13/0.99  ------ Global Options
% 2.13/0.99  
% 2.13/0.99  --schedule                              default
% 2.13/0.99  --add_important_lit                     false
% 2.13/0.99  --prop_solver_per_cl                    1000
% 2.13/0.99  --min_unsat_core                        false
% 2.13/0.99  --soft_assumptions                      false
% 2.13/0.99  --soft_lemma_size                       3
% 2.13/0.99  --prop_impl_unit_size                   0
% 2.13/0.99  --prop_impl_unit                        []
% 2.13/0.99  --share_sel_clauses                     true
% 2.13/0.99  --reset_solvers                         false
% 2.13/0.99  --bc_imp_inh                            [conj_cone]
% 2.13/0.99  --conj_cone_tolerance                   3.
% 2.13/0.99  --extra_neg_conj                        none
% 2.13/0.99  --large_theory_mode                     true
% 2.13/0.99  --prolific_symb_bound                   200
% 2.13/0.99  --lt_threshold                          2000
% 2.13/0.99  --clause_weak_htbl                      true
% 2.13/0.99  --gc_record_bc_elim                     false
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing Options
% 2.13/0.99  
% 2.13/0.99  --preprocessing_flag                    true
% 2.13/0.99  --time_out_prep_mult                    0.1
% 2.13/0.99  --splitting_mode                        input
% 2.13/0.99  --splitting_grd                         true
% 2.13/0.99  --splitting_cvd                         false
% 2.13/0.99  --splitting_cvd_svl                     false
% 2.13/0.99  --splitting_nvd                         32
% 2.13/0.99  --sub_typing                            true
% 2.13/0.99  --prep_gs_sim                           true
% 2.13/0.99  --prep_unflatten                        true
% 2.13/0.99  --prep_res_sim                          true
% 2.13/0.99  --prep_upred                            true
% 2.13/0.99  --prep_sem_filter                       exhaustive
% 2.13/0.99  --prep_sem_filter_out                   false
% 2.13/0.99  --pred_elim                             true
% 2.13/0.99  --res_sim_input                         true
% 2.13/0.99  --eq_ax_congr_red                       true
% 2.13/0.99  --pure_diseq_elim                       true
% 2.13/0.99  --brand_transform                       false
% 2.13/0.99  --non_eq_to_eq                          false
% 2.13/0.99  --prep_def_merge                        true
% 2.13/0.99  --prep_def_merge_prop_impl              false
% 2.13/0.99  --prep_def_merge_mbd                    true
% 2.13/0.99  --prep_def_merge_tr_red                 false
% 2.13/0.99  --prep_def_merge_tr_cl                  false
% 2.13/0.99  --smt_preprocessing                     true
% 2.13/0.99  --smt_ac_axioms                         fast
% 2.13/0.99  --preprocessed_out                      false
% 2.13/0.99  --preprocessed_stats                    false
% 2.13/0.99  
% 2.13/0.99  ------ Abstraction refinement Options
% 2.13/0.99  
% 2.13/0.99  --abstr_ref                             []
% 2.13/0.99  --abstr_ref_prep                        false
% 2.13/0.99  --abstr_ref_until_sat                   false
% 2.13/0.99  --abstr_ref_sig_restrict                funpre
% 2.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.99  --abstr_ref_under                       []
% 2.13/0.99  
% 2.13/0.99  ------ SAT Options
% 2.13/0.99  
% 2.13/0.99  --sat_mode                              false
% 2.13/0.99  --sat_fm_restart_options                ""
% 2.13/0.99  --sat_gr_def                            false
% 2.13/0.99  --sat_epr_types                         true
% 2.13/0.99  --sat_non_cyclic_types                  false
% 2.13/0.99  --sat_finite_models                     false
% 2.13/0.99  --sat_fm_lemmas                         false
% 2.13/0.99  --sat_fm_prep                           false
% 2.13/0.99  --sat_fm_uc_incr                        true
% 2.13/0.99  --sat_out_model                         small
% 2.13/0.99  --sat_out_clauses                       false
% 2.13/0.99  
% 2.13/0.99  ------ QBF Options
% 2.13/0.99  
% 2.13/0.99  --qbf_mode                              false
% 2.13/0.99  --qbf_elim_univ                         false
% 2.13/0.99  --qbf_dom_inst                          none
% 2.13/0.99  --qbf_dom_pre_inst                      false
% 2.13/0.99  --qbf_sk_in                             false
% 2.13/0.99  --qbf_pred_elim                         true
% 2.13/0.99  --qbf_split                             512
% 2.13/0.99  
% 2.13/0.99  ------ BMC1 Options
% 2.13/0.99  
% 2.13/0.99  --bmc1_incremental                      false
% 2.13/0.99  --bmc1_axioms                           reachable_all
% 2.13/0.99  --bmc1_min_bound                        0
% 2.13/0.99  --bmc1_max_bound                        -1
% 2.13/0.99  --bmc1_max_bound_default                -1
% 2.13/0.99  --bmc1_symbol_reachability              true
% 2.13/0.99  --bmc1_property_lemmas                  false
% 2.13/1.00  --bmc1_k_induction                      false
% 2.13/1.00  --bmc1_non_equiv_states                 false
% 2.13/1.00  --bmc1_deadlock                         false
% 2.13/1.00  --bmc1_ucm                              false
% 2.13/1.00  --bmc1_add_unsat_core                   none
% 2.13/1.00  --bmc1_unsat_core_children              false
% 2.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/1.00  --bmc1_out_stat                         full
% 2.13/1.00  --bmc1_ground_init                      false
% 2.13/1.00  --bmc1_pre_inst_next_state              false
% 2.13/1.00  --bmc1_pre_inst_state                   false
% 2.13/1.00  --bmc1_pre_inst_reach_state             false
% 2.13/1.00  --bmc1_out_unsat_core                   false
% 2.13/1.00  --bmc1_aig_witness_out                  false
% 2.13/1.00  --bmc1_verbose                          false
% 2.13/1.00  --bmc1_dump_clauses_tptp                false
% 2.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.13/1.00  --bmc1_dump_file                        -
% 2.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.13/1.00  --bmc1_ucm_extend_mode                  1
% 2.13/1.00  --bmc1_ucm_init_mode                    2
% 2.13/1.00  --bmc1_ucm_cone_mode                    none
% 2.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.13/1.00  --bmc1_ucm_relax_model                  4
% 2.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/1.00  --bmc1_ucm_layered_model                none
% 2.13/1.00  --bmc1_ucm_max_lemma_size               10
% 2.13/1.00  
% 2.13/1.00  ------ AIG Options
% 2.13/1.00  
% 2.13/1.00  --aig_mode                              false
% 2.13/1.00  
% 2.13/1.00  ------ Instantiation Options
% 2.13/1.00  
% 2.13/1.00  --instantiation_flag                    true
% 2.13/1.00  --inst_sos_flag                         false
% 2.13/1.00  --inst_sos_phase                        true
% 2.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel_side                     none
% 2.13/1.00  --inst_solver_per_active                1400
% 2.13/1.00  --inst_solver_calls_frac                1.
% 2.13/1.00  --inst_passive_queue_type               priority_queues
% 2.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/1.00  --inst_passive_queues_freq              [25;2]
% 2.13/1.00  --inst_dismatching                      true
% 2.13/1.00  --inst_eager_unprocessed_to_passive     true
% 2.13/1.00  --inst_prop_sim_given                   true
% 2.13/1.00  --inst_prop_sim_new                     false
% 2.13/1.00  --inst_subs_new                         false
% 2.13/1.00  --inst_eq_res_simp                      false
% 2.13/1.00  --inst_subs_given                       false
% 2.13/1.00  --inst_orphan_elimination               true
% 2.13/1.00  --inst_learning_loop_flag               true
% 2.13/1.00  --inst_learning_start                   3000
% 2.13/1.00  --inst_learning_factor                  2
% 2.13/1.00  --inst_start_prop_sim_after_learn       3
% 2.13/1.00  --inst_sel_renew                        solver
% 2.13/1.00  --inst_lit_activity_flag                true
% 2.13/1.00  --inst_restr_to_given                   false
% 2.13/1.00  --inst_activity_threshold               500
% 2.13/1.00  --inst_out_proof                        true
% 2.13/1.00  
% 2.13/1.00  ------ Resolution Options
% 2.13/1.00  
% 2.13/1.00  --resolution_flag                       false
% 2.13/1.00  --res_lit_sel                           adaptive
% 2.13/1.00  --res_lit_sel_side                      none
% 2.13/1.00  --res_ordering                          kbo
% 2.13/1.00  --res_to_prop_solver                    active
% 2.13/1.00  --res_prop_simpl_new                    false
% 2.13/1.00  --res_prop_simpl_given                  true
% 2.13/1.00  --res_passive_queue_type                priority_queues
% 2.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/1.00  --res_passive_queues_freq               [15;5]
% 2.13/1.00  --res_forward_subs                      full
% 2.13/1.00  --res_backward_subs                     full
% 2.13/1.00  --res_forward_subs_resolution           true
% 2.13/1.00  --res_backward_subs_resolution          true
% 2.13/1.00  --res_orphan_elimination                true
% 2.13/1.00  --res_time_limit                        2.
% 2.13/1.00  --res_out_proof                         true
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Options
% 2.13/1.00  
% 2.13/1.00  --superposition_flag                    true
% 2.13/1.00  --sup_passive_queue_type                priority_queues
% 2.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.13/1.00  --demod_completeness_check              fast
% 2.13/1.00  --demod_use_ground                      true
% 2.13/1.00  --sup_to_prop_solver                    passive
% 2.13/1.00  --sup_prop_simpl_new                    true
% 2.13/1.00  --sup_prop_simpl_given                  true
% 2.13/1.00  --sup_fun_splitting                     false
% 2.13/1.00  --sup_smt_interval                      50000
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Simplification Setup
% 2.13/1.00  
% 2.13/1.00  --sup_indices_passive                   []
% 2.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_full_bw                           [BwDemod]
% 2.13/1.00  --sup_immed_triv                        [TrivRules]
% 2.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_immed_bw_main                     []
% 2.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  
% 2.13/1.00  ------ Combination Options
% 2.13/1.00  
% 2.13/1.00  --comb_res_mult                         3
% 2.13/1.00  --comb_sup_mult                         2
% 2.13/1.00  --comb_inst_mult                        10
% 2.13/1.00  
% 2.13/1.00  ------ Debug Options
% 2.13/1.00  
% 2.13/1.00  --dbg_backtrace                         false
% 2.13/1.00  --dbg_dump_prop_clauses                 false
% 2.13/1.00  --dbg_dump_prop_clauses_file            -
% 2.13/1.00  --dbg_out_stat                          false
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  ------ Proving...
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  % SZS status Theorem for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  fof(f8,conjecture,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f9,negated_conjecture,(
% 2.13/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.13/1.00    inference(negated_conjecture,[],[f8])).
% 2.13/1.00  
% 2.13/1.00  fof(f21,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f9])).
% 2.13/1.00  
% 2.13/1.00  fof(f22,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.13/1.00    inference(flattening,[],[f21])).
% 2.13/1.00  
% 2.13/1.00  fof(f25,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.13/1.00    inference(nnf_transformation,[],[f22])).
% 2.13/1.00  
% 2.13/1.00  fof(f26,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.13/1.00    inference(flattening,[],[f25])).
% 2.13/1.00  
% 2.13/1.00  fof(f30,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK3 = X2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK3))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f29,plain,(
% 2.13/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f28,plain,(
% 2.13/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,X0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,X0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f27,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f31,plain,(
% 2.13/1.00    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f30,f29,f28,f27])).
% 2.13/1.00  
% 2.13/1.00  fof(f47,plain,(
% 2.13/1.00    l1_pre_topc(sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f3,axiom,(
% 2.13/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f13,plain,(
% 2.13/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(ennf_transformation,[],[f3])).
% 2.13/1.00  
% 2.13/1.00  fof(f35,plain,(
% 2.13/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f13])).
% 2.13/1.00  
% 2.13/1.00  fof(f2,axiom,(
% 2.13/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f12,plain,(
% 2.13/1.00    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.13/1.00    inference(ennf_transformation,[],[f2])).
% 2.13/1.00  
% 2.13/1.00  fof(f34,plain,(
% 2.13/1.00    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.13/1.00    inference(cnf_transformation,[],[f12])).
% 2.13/1.00  
% 2.13/1.00  fof(f1,axiom,(
% 2.13/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f10,plain,(
% 2.13/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(ennf_transformation,[],[f1])).
% 2.13/1.00  
% 2.13/1.00  fof(f11,plain,(
% 2.13/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(flattening,[],[f10])).
% 2.13/1.00  
% 2.13/1.00  fof(f32,plain,(
% 2.13/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f11])).
% 2.13/1.00  
% 2.13/1.00  fof(f33,plain,(
% 2.13/1.00    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.13/1.00    inference(cnf_transformation,[],[f12])).
% 2.13/1.00  
% 2.13/1.00  fof(f5,axiom,(
% 2.13/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f16,plain,(
% 2.13/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.13/1.00    inference(ennf_transformation,[],[f5])).
% 2.13/1.00  
% 2.13/1.00  fof(f38,plain,(
% 2.13/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.13/1.00    inference(cnf_transformation,[],[f16])).
% 2.13/1.00  
% 2.13/1.00  fof(f53,plain,(
% 2.13/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f6,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f17,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f6])).
% 2.13/1.00  
% 2.13/1.00  fof(f18,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.13/1.00    inference(flattening,[],[f17])).
% 2.13/1.00  
% 2.13/1.00  fof(f23,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.13/1.00    inference(nnf_transformation,[],[f18])).
% 2.13/1.00  
% 2.13/1.00  fof(f41,plain,(
% 2.13/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f23])).
% 2.13/1.00  
% 2.13/1.00  fof(f57,plain,(
% 2.13/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.00    inference(equality_resolution,[],[f41])).
% 2.13/1.00  
% 2.13/1.00  fof(f55,plain,(
% 2.13/1.00    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f54,plain,(
% 2.13/1.00    sK2 = sK3),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f7,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f19,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f7])).
% 2.13/1.00  
% 2.13/1.00  fof(f20,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.13/1.00    inference(flattening,[],[f19])).
% 2.13/1.00  
% 2.13/1.00  fof(f24,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.13/1.00    inference(nnf_transformation,[],[f20])).
% 2.13/1.00  
% 2.13/1.00  fof(f43,plain,(
% 2.13/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f24])).
% 2.13/1.00  
% 2.13/1.00  fof(f59,plain,(
% 2.13/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.00    inference(equality_resolution,[],[f43])).
% 2.13/1.00  
% 2.13/1.00  fof(f44,plain,(
% 2.13/1.00    v2_pre_topc(sK0)),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f45,plain,(
% 2.13/1.00    l1_pre_topc(sK0)),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f46,plain,(
% 2.13/1.00    v2_pre_topc(sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f51,plain,(
% 2.13/1.00    v1_funct_1(sK3)),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f52,plain,(
% 2.13/1.00    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f4,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f14,plain,(
% 2.13/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f4])).
% 2.13/1.00  
% 2.13/1.00  fof(f15,plain,(
% 2.13/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.13/1.00    inference(flattening,[],[f14])).
% 2.13/1.00  
% 2.13/1.00  fof(f37,plain,(
% 2.13/1.00    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f15])).
% 2.13/1.00  
% 2.13/1.00  fof(f40,plain,(
% 2.13/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f23])).
% 2.13/1.00  
% 2.13/1.00  fof(f58,plain,(
% 2.13/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.00    inference(equality_resolution,[],[f40])).
% 2.13/1.00  
% 2.13/1.00  fof(f42,plain,(
% 2.13/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f24])).
% 2.13/1.00  
% 2.13/1.00  fof(f60,plain,(
% 2.13/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/1.00    inference(equality_resolution,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f56,plain,(
% 2.13/1.00    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f49,plain,(
% 2.13/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f50,plain,(
% 2.13/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  cnf(c_21,negated_conjecture,
% 2.13/1.00      ( l1_pre_topc(sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1345,plain,
% 2.13/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.13/1.00      | ~ l1_pre_topc(X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1362,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.13/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1364,plain,
% 2.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1841,plain,
% 2.13/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_1362,c_1364]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_0,plain,
% 2.13/1.00      ( ~ l1_pre_topc(X0)
% 2.13/1.00      | ~ v1_pre_topc(X0)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.13/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1365,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 2.13/1.00      | l1_pre_topc(X0) != iProver_top
% 2.13/1.00      | v1_pre_topc(X0) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2099,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 2.13/1.00      | l1_pre_topc(X0) != iProver_top
% 2.13/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_1841,c_1365]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1615,plain,
% 2.13/1.00      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.13/1.00      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.13/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1616,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 2.13/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1615]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.13/1.00      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1363,plain,
% 2.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.13/1.00      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1834,plain,
% 2.13/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.13/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_1362,c_1363]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2485,plain,
% 2.13/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.13/1.00      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_2099,c_1616,c_1834,c_1841]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2486,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 2.13/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.13/1.00      inference(renaming,[status(thm)],[c_2485]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2493,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_1345,c_2486]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_7,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.13/1.00      | X2 = X1
% 2.13/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1358,plain,
% 2.13/1.00      ( X0 = X1
% 2.13/1.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.13/1.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2603,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 2.13/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
% 2.13/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_2493,c_1358]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_28,plain,
% 2.13/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1586,plain,
% 2.13/1.00      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2080,plain,
% 2.13/1.00      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_1586]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2081,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2080]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2375,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 2.13/1.00      | ~ l1_pre_topc(sK1) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2376,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2375]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2386,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 2.13/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2391,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_2386]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2604,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 2.13/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
% 2.13/1.00      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_2493,c_1358]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3110,plain,
% 2.13/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_2603,c_28,c_2081,c_2376,c_2391,c_2604]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3111,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 2.13/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0 ),
% 2.13/1.00      inference(renaming,[status(thm)],[c_3110]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3117,plain,
% 2.13/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
% 2.13/1.00      inference(equality_resolution,[status(thm)],[c_3111]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_15,negated_conjecture,
% 2.13/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 2.13/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1351,plain,
% 2.13/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3705,plain,
% 2.13/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) = iProver_top ),
% 2.13/1.00      inference(demodulation,[status(thm)],[c_3117,c_1351]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_8,plain,
% 2.13/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.13/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 2.13/1.00      | v5_pre_topc(X0,X1,X2)
% 2.13/1.00      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 2.13/1.00      | ~ v1_funct_1(X0)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2) ),
% 2.13/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1357,plain,
% 2.13/1.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 2.13/1.00      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 2.13/1.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 2.13/1.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 2.13/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 2.13/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 2.13/1.00      | v1_funct_1(X0) != iProver_top
% 2.13/1.00      | v2_pre_topc(X1) != iProver_top
% 2.13/1.00      | v2_pre_topc(X2) != iProver_top
% 2.13/1.00      | l1_pre_topc(X1) != iProver_top
% 2.13/1.00      | l1_pre_topc(X2) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_4155,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 2.13/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.13/1.00      | v1_funct_1(sK3) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_3705,c_1357]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_13,negated_conjecture,
% 2.13/1.00      ( v5_pre_topc(sK2,sK0,sK1)
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 2.13/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1352,plain,
% 2.13/1.00      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_14,negated_conjecture,
% 2.13/1.00      ( sK2 = sK3 ),
% 2.13/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1419,plain,
% 2.13/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_1352,c_14]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_10,plain,
% 2.13/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.13/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 2.13/1.00      | v5_pre_topc(X0,X1,X2)
% 2.13/1.00      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 2.13/1.00      | ~ v1_funct_1(X0)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2) ),
% 2.13/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1355,plain,
% 2.13/1.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 2.13/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 2.13/1.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 2.13/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 2.13/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 2.13/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 2.13/1.00      | v1_funct_1(X0) != iProver_top
% 2.13/1.00      | v2_pre_topc(X1) != iProver_top
% 2.13/1.00      | v2_pre_topc(X2) != iProver_top
% 2.13/1.00      | l1_pre_topc(X1) != iProver_top
% 2.13/1.00      | l1_pre_topc(X2) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2882,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 2.13/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 2.13/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 2.13/1.00      | v1_funct_1(sK3) != iProver_top
% 2.13/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_1351,c_1355]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_24,negated_conjecture,
% 2.13/1.00      ( v2_pre_topc(sK0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_25,plain,
% 2.13/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_23,negated_conjecture,
% 2.13/1.00      ( l1_pre_topc(sK0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_26,plain,
% 2.13/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_22,negated_conjecture,
% 2.13/1.00      ( v2_pre_topc(sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_27,plain,
% 2.13/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_17,negated_conjecture,
% 2.13/1.00      ( v1_funct_1(sK3) ),
% 2.13/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_32,plain,
% 2.13/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_16,negated_conjecture,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 2.13/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_33,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_4,plain,
% 2.13/1.00      ( ~ v2_pre_topc(X0)
% 2.13/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 2.13/1.00      | ~ l1_pre_topc(X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_56,plain,
% 2.13/1.00      ( v2_pre_topc(X0) != iProver_top
% 2.13/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 2.13/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_58,plain,
% 2.13/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 2.13/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_56]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_59,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.13/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_61,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.13/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_59]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1587,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1586]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1589,plain,
% 2.13/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_1587]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3218,plain,
% 2.13/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.13/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_2882,c_25,c_26,c_27,c_28,c_32,c_33,c_58,c_61,c_1589]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3219,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 2.13/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 2.13/1.00      inference(renaming,[status(thm)],[c_3218]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3226,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 2.13/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_1419,c_3219]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_4157,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_3705,c_3226]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_4201,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 2.13/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.13/1.00      | v1_funct_1(sK3) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.13/1.00      inference(forward_subsumption_resolution,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_4155,c_4157]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_9,plain,
% 2.13/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.13/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 2.13/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 2.13/1.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 2.13/1.00      | ~ v1_funct_1(X0)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2) ),
% 2.13/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1356,plain,
% 2.13/1.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 2.13/1.00      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 2.13/1.00      | v5_pre_topc(X0,X1,X2) != iProver_top
% 2.13/1.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 2.13/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 2.13/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 2.13/1.00      | v1_funct_1(X0) != iProver_top
% 2.13/1.00      | v2_pre_topc(X1) != iProver_top
% 2.13/1.00      | v2_pre_topc(X2) != iProver_top
% 2.13/1.00      | l1_pre_topc(X1) != iProver_top
% 2.13/1.00      | l1_pre_topc(X2) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_4156,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 2.13/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.13/1.00      | v1_funct_1(sK3) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_3705,c_1356]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_4181,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 2.13/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.13/1.00      | v1_funct_1(sK3) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.13/1.00      inference(forward_subsumption_resolution,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_4156,c_4157]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1350,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3706,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) = iProver_top ),
% 2.13/1.00      inference(demodulation,[status(thm)],[c_3117,c_1350]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_11,plain,
% 2.13/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.13/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 2.13/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 2.13/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 2.13/1.00      | ~ v1_funct_1(X0)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ v2_pre_topc(X2)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X2) ),
% 2.13/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1354,plain,
% 2.13/1.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 2.13/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 2.13/1.00      | v5_pre_topc(X0,X1,X2) != iProver_top
% 2.13/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 2.13/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 2.13/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 2.13/1.00      | v1_funct_1(X0) != iProver_top
% 2.13/1.00      | v2_pre_topc(X1) != iProver_top
% 2.13/1.00      | v2_pre_topc(X2) != iProver_top
% 2.13/1.00      | l1_pre_topc(X1) != iProver_top
% 2.13/1.00      | l1_pre_topc(X2) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2364,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 2.13/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 2.13/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 2.13/1.00      | v1_funct_1(sK3) != iProver_top
% 2.13/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.13/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.13/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.13/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.13/1.00      inference(superposition,[status(thm)],[c_1351,c_1354]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2476,plain,
% 2.13/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.13/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_2364,c_25,c_26,c_27,c_28,c_32,c_33,c_58,c_61,c_1589]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2477,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 2.13/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 2.13/1.00      inference(renaming,[status(thm)],[c_2476]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_12,negated_conjecture,
% 2.13/1.00      ( ~ v5_pre_topc(sK2,sK0,sK1)
% 2.13/1.00      | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 2.13/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1353,plain,
% 2.13/1.00      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1436,plain,
% 2.13/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 2.13/1.00      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_1353,c_14]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_19,negated_conjecture,
% 2.13/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1347,plain,
% 2.13/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1379,plain,
% 2.13/1.00      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_1347,c_14]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_18,negated_conjecture,
% 2.13/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.13/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1348,plain,
% 2.13/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1382,plain,
% 2.13/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_1348,c_14]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(contradiction,plain,
% 2.13/1.00      ( $false ),
% 2.13/1.00      inference(minisat,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_4201,c_4181,c_3706,c_3705,c_2477,c_1436,c_1379,c_1382,
% 2.13/1.00                 c_32,c_28,c_27,c_26,c_25]) ).
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  ------                               Statistics
% 2.13/1.00  
% 2.13/1.00  ------ General
% 2.13/1.00  
% 2.13/1.00  abstr_ref_over_cycles:                  0
% 2.13/1.00  abstr_ref_under_cycles:                 0
% 2.13/1.00  gc_basic_clause_elim:                   0
% 2.13/1.00  forced_gc_time:                         0
% 2.13/1.00  parsing_time:                           0.01
% 2.13/1.00  unif_index_cands_time:                  0.
% 2.13/1.00  unif_index_add_time:                    0.
% 2.13/1.00  orderings_time:                         0.
% 2.13/1.00  out_proof_time:                         0.01
% 2.13/1.00  total_time:                             0.152
% 2.13/1.00  num_of_symbols:                         47
% 2.13/1.00  num_of_terms:                           3470
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing
% 2.13/1.00  
% 2.13/1.00  num_of_splits:                          0
% 2.13/1.00  num_of_split_atoms:                     0
% 2.13/1.00  num_of_reused_defs:                     0
% 2.13/1.00  num_eq_ax_congr_red:                    0
% 2.13/1.00  num_of_sem_filtered_clauses:            1
% 2.13/1.00  num_of_subtypes:                        0
% 2.13/1.00  monotx_restored_types:                  0
% 2.13/1.00  sat_num_of_epr_types:                   0
% 2.13/1.00  sat_num_of_non_cyclic_types:            0
% 2.13/1.00  sat_guarded_non_collapsed_types:        0
% 2.13/1.00  num_pure_diseq_elim:                    0
% 2.13/1.00  simp_replaced_by:                       0
% 2.13/1.00  res_preprocessed:                       104
% 2.13/1.00  prep_upred:                             0
% 2.13/1.00  prep_unflattend:                        10
% 2.13/1.00  smt_new_axioms:                         0
% 2.13/1.00  pred_elim_cands:                        7
% 2.13/1.00  pred_elim:                              0
% 2.13/1.00  pred_elim_cl:                           0
% 2.13/1.00  pred_elim_cycles:                       2
% 2.13/1.00  merged_defs:                            6
% 2.13/1.00  merged_defs_ncl:                        0
% 2.13/1.00  bin_hyper_res:                          6
% 2.13/1.00  prep_cycles:                            3
% 2.13/1.00  pred_elim_time:                         0.01
% 2.13/1.00  splitting_time:                         0.
% 2.13/1.00  sem_filter_time:                        0.
% 2.13/1.00  monotx_time:                            0.001
% 2.13/1.00  subtype_inf_time:                       0.
% 2.13/1.00  
% 2.13/1.00  ------ Problem properties
% 2.13/1.00  
% 2.13/1.00  clauses:                                25
% 2.13/1.00  conjectures:                            13
% 2.13/1.00  epr:                                    7
% 2.13/1.00  horn:                                   24
% 2.13/1.00  ground:                                 13
% 2.13/1.00  unary:                                  11
% 2.13/1.00  binary:                                 5
% 2.13/1.00  lits:                                   80
% 2.13/1.00  lits_eq:                                6
% 2.13/1.00  fd_pure:                                0
% 2.13/1.00  fd_pseudo:                              0
% 2.13/1.00  fd_cond:                                0
% 2.13/1.00  fd_pseudo_cond:                         2
% 2.13/1.00  ac_symbols:                             0
% 2.13/1.00  
% 2.13/1.00  ------ Propositional Solver
% 2.13/1.00  
% 2.13/1.00  prop_solver_calls:                      23
% 2.13/1.00  prop_fast_solver_calls:                 934
% 2.13/1.00  smt_solver_calls:                       0
% 2.13/1.00  smt_fast_solver_calls:                  0
% 2.13/1.00  prop_num_of_clauses:                    1103
% 2.13/1.00  prop_preprocess_simplified:             3633
% 2.13/1.00  prop_fo_subsumed:                       33
% 2.13/1.00  prop_solver_time:                       0.
% 2.13/1.00  smt_solver_time:                        0.
% 2.13/1.00  smt_fast_solver_time:                   0.
% 2.13/1.00  prop_fast_solver_time:                  0.
% 2.13/1.00  prop_unsat_core_time:                   0.
% 2.13/1.00  
% 2.13/1.00  ------ QBF
% 2.13/1.00  
% 2.13/1.00  qbf_q_res:                              0
% 2.13/1.00  qbf_num_tautologies:                    0
% 2.13/1.00  qbf_prep_cycles:                        0
% 2.13/1.00  
% 2.13/1.00  ------ BMC1
% 2.13/1.00  
% 2.13/1.00  bmc1_current_bound:                     -1
% 2.13/1.00  bmc1_last_solved_bound:                 -1
% 2.13/1.00  bmc1_unsat_core_size:                   -1
% 2.13/1.00  bmc1_unsat_core_parents_size:           -1
% 2.13/1.00  bmc1_merge_next_fun:                    0
% 2.13/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.13/1.00  
% 2.13/1.00  ------ Instantiation
% 2.13/1.00  
% 2.13/1.00  inst_num_of_clauses:                    322
% 2.13/1.00  inst_num_in_passive:                    46
% 2.13/1.00  inst_num_in_active:                     222
% 2.13/1.00  inst_num_in_unprocessed:                55
% 2.13/1.00  inst_num_of_loops:                      240
% 2.13/1.00  inst_num_of_learning_restarts:          0
% 2.13/1.00  inst_num_moves_active_passive:          15
% 2.13/1.00  inst_lit_activity:                      0
% 2.13/1.00  inst_lit_activity_moves:                0
% 2.13/1.00  inst_num_tautologies:                   0
% 2.13/1.00  inst_num_prop_implied:                  0
% 2.13/1.00  inst_num_existing_simplified:           0
% 2.13/1.00  inst_num_eq_res_simplified:             0
% 2.13/1.00  inst_num_child_elim:                    0
% 2.13/1.00  inst_num_of_dismatching_blockings:      158
% 2.13/1.00  inst_num_of_non_proper_insts:           470
% 2.13/1.00  inst_num_of_duplicates:                 0
% 2.13/1.00  inst_inst_num_from_inst_to_res:         0
% 2.13/1.00  inst_dismatching_checking_time:         0.
% 2.13/1.00  
% 2.13/1.00  ------ Resolution
% 2.13/1.00  
% 2.13/1.00  res_num_of_clauses:                     0
% 2.13/1.00  res_num_in_passive:                     0
% 2.13/1.00  res_num_in_active:                      0
% 2.13/1.00  res_num_of_loops:                       107
% 2.13/1.00  res_forward_subset_subsumed:            55
% 2.13/1.00  res_backward_subset_subsumed:           2
% 2.13/1.00  res_forward_subsumed:                   0
% 2.13/1.00  res_backward_subsumed:                  0
% 2.13/1.00  res_forward_subsumption_resolution:     0
% 2.13/1.00  res_backward_subsumption_resolution:    0
% 2.13/1.00  res_clause_to_clause_subsumption:       203
% 2.13/1.00  res_orphan_elimination:                 0
% 2.13/1.00  res_tautology_del:                      62
% 2.13/1.00  res_num_eq_res_simplified:              0
% 2.13/1.00  res_num_sel_changes:                    0
% 2.13/1.00  res_moves_from_active_to_pass:          0
% 2.13/1.00  
% 2.13/1.00  ------ Superposition
% 2.13/1.00  
% 2.13/1.00  sup_time_total:                         0.
% 2.13/1.00  sup_time_generating:                    0.
% 2.13/1.00  sup_time_sim_full:                      0.
% 2.13/1.00  sup_time_sim_immed:                     0.
% 2.13/1.00  
% 2.13/1.00  sup_num_of_clauses:                     71
% 2.13/1.00  sup_num_in_active:                      35
% 2.13/1.00  sup_num_in_passive:                     36
% 2.13/1.00  sup_num_of_loops:                       47
% 2.13/1.00  sup_fw_superposition:                   31
% 2.13/1.00  sup_bw_superposition:                   37
% 2.13/1.00  sup_immediate_simplified:               24
% 2.13/1.00  sup_given_eliminated:                   4
% 2.13/1.00  comparisons_done:                       0
% 2.13/1.00  comparisons_avoided:                    0
% 2.13/1.00  
% 2.13/1.00  ------ Simplifications
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  sim_fw_subset_subsumed:                 0
% 2.13/1.00  sim_bw_subset_subsumed:                 6
% 2.13/1.00  sim_fw_subsumed:                        0
% 2.13/1.00  sim_bw_subsumed:                        0
% 2.13/1.00  sim_fw_subsumption_res:                 2
% 2.13/1.00  sim_bw_subsumption_res:                 0
% 2.13/1.00  sim_tautology_del:                      13
% 2.13/1.00  sim_eq_tautology_del:                   8
% 2.13/1.00  sim_eq_res_simp:                        0
% 2.13/1.00  sim_fw_demodulated:                     0
% 2.13/1.00  sim_bw_demodulated:                     11
% 2.13/1.00  sim_light_normalised:                   27
% 2.13/1.00  sim_joinable_taut:                      0
% 2.13/1.00  sim_joinable_simp:                      0
% 2.13/1.00  sim_ac_normalised:                      0
% 2.13/1.00  sim_smt_subsumption:                    0
% 2.13/1.00  
%------------------------------------------------------------------------------
