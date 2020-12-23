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
% DateTime   : Thu Dec  3 12:11:55 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  312 (61915 expanded)
%              Number of clauses        :  226 (15178 expanded)
%              Number of leaves         :   18 (17776 expanded)
%              Depth                    :   36
%              Number of atoms          : 1249 (683517 expanded)
%              Number of equality atoms :  555 (87873 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f46,f45,f44,f43])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f35])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f53])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f68])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f67,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f52])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2220,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2230,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6336,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2220,c_2230])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2236,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3736,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2220,c_2236])).

cnf(c_6343,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6336,c_3736])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6350,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6343])).

cnf(c_7393,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6343,c_28,c_6350])).

cnf(c_7394,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_7393])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2238,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2896,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2220,c_2238])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2242,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4038,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2896,c_2242])).

cnf(c_7423,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_4038])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7430,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7423,c_3])).

cnf(c_2564,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2565,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2564])).

cnf(c_2567,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2565])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3103,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3104,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3103])).

cnf(c_8562,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7430,c_2567,c_3104])).

cnf(c_8563,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_8562])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2241,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3735,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2239,c_2236])).

cnf(c_5894,plain,
    ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2241,c_3735])).

cnf(c_8568,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) ),
    inference(superposition,[status(thm)],[c_8563,c_5894])).

cnf(c_8581,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_8568,c_3736])).

cnf(c_8902,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_7394,c_8581])).

cnf(c_8904,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8902,c_3])).

cnf(c_9049,plain,
    ( k1_relset_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8904,c_3736])).

cnf(c_2219,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9053,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8904,c_2219])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2217,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2245,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2217,c_26])).

cnf(c_6337,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2245,c_2230])).

cnf(c_3737,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2245,c_2236])).

cnf(c_6342,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6337,c_3737])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2216,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2244,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2216,c_26])).

cnf(c_6558,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6342,c_2244])).

cnf(c_6559,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_6558])).

cnf(c_2897,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2245,c_2238])).

cnf(c_4039,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2897,c_2242])).

cnf(c_6580,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6559,c_4039])).

cnf(c_6600,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3)
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6580,c_3])).

cnf(c_7193,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6600,c_2567,c_3104])).

cnf(c_7194,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_7193])).

cnf(c_7197,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_7194,c_5894])).

cnf(c_7204,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_7197,c_3737])).

cnf(c_7368,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6559,c_7204])).

cnf(c_7369,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7368,c_3])).

cnf(c_9052,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8904,c_2220])).

cnf(c_21,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2225,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4415,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2220,c_2225])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_44,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_45,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2221,plain,
    ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2247,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2221,c_26])).

cnf(c_24,negated_conjecture,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2222,plain,
    ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2248,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2222,c_26])).

cnf(c_19,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2392,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2393,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2392])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2503,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2504,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2503])).

cnf(c_18,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2655,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2656,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2655])).

cnf(c_22,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2542,plain,
    ( ~ v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,X0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3023,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2542])).

cnf(c_3024,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3023])).

cnf(c_20,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2770,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
    | v5_pre_topc(sK3,sK0,X0)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3056,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2770])).

cnf(c_3057,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3056])).

cnf(c_23,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2980,plain,
    ( ~ v5_pre_topc(sK3,sK0,X0)
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4421,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2980])).

cnf(c_4422,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4421])).

cnf(c_4679,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4415,c_37,c_38,c_39,c_40,c_44,c_45,c_46,c_2247,c_2245,c_2244,c_2248,c_2393,c_2504,c_2656,c_3024,c_3057,c_4422])).

cnf(c_4680,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4679])).

cnf(c_4683,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4680,c_37,c_38,c_39,c_40,c_44,c_45,c_46,c_2247,c_2245,c_2244,c_2393,c_2504,c_2656,c_3057,c_4422])).

cnf(c_7775,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7369,c_4683])).

cnf(c_9506,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9052,c_7775])).

cnf(c_9582,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7369,c_9506])).

cnf(c_9586,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9049,c_9053,c_9582])).

cnf(c_2224,plain,
    ( v5_pre_topc(X0,X1,X2) = iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3727,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2220,c_2224])).

cnf(c_2377,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2378,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2377])).

cnf(c_2491,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2492,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2491])).

cnf(c_2644,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2645,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2644])).

cnf(c_2223,plain,
    ( v5_pre_topc(X0,X1,X2) != iProver_top
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3094,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2220,c_2223])).

cnf(c_3047,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2770])).

cnf(c_3048,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3047])).

cnf(c_3269,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3094,c_37,c_38,c_39,c_40,c_44,c_45,c_2245,c_2244,c_2248,c_2378,c_2492,c_2645,c_3048])).

cnf(c_3270,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3269])).

cnf(c_4086,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3727,c_37,c_38,c_39,c_40,c_44,c_45,c_2245,c_2244,c_2248,c_2378,c_2492,c_2645,c_3048,c_3094])).

cnf(c_4087,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4086])).

cnf(c_6582,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6559,c_4087])).

cnf(c_4090,plain,
    ( v5_pre_topc(sK3,sK0,sK1) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2247,c_4087])).

cnf(c_2964,plain,
    ( ~ v5_pre_topc(sK3,X0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4398,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2964])).

cnf(c_4399,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
    | v5_pre_topc(sK3,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4398])).

cnf(c_6941,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6582,c_37,c_38,c_39,c_40,c_44,c_2245,c_2244,c_3270,c_4090,c_4399])).

cnf(c_6946,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6559,c_6941])).

cnf(c_6947,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6946,c_3])).

cnf(c_6593,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6559,c_2245])).

cnf(c_6595,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6593,c_3])).

cnf(c_8085,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
    | u1_struct_0(sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6947,c_6595])).

cnf(c_8086,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8085])).

cnf(c_9595,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9586,c_8086])).

cnf(c_101,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_100,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_102,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_103,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_13,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2233,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2250,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2233,c_4])).

cnf(c_2259,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2250])).

cnf(c_2261,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_7427,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_2219])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2234,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2251,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2234,c_3])).

cnf(c_7614,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7427,c_2251])).

cnf(c_2578,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2579,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2578])).

cnf(c_2581,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2579])).

cnf(c_8368,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8369,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8368])).

cnf(c_8371,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8369])).

cnf(c_8906,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7614,c_2567,c_2581,c_3104,c_8371])).

cnf(c_9614,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_9586,c_6559])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2237,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4469,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_2238])).

cnf(c_10864,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relset_1(X1,k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_4469])).

cnf(c_2240,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2895,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_2238])).

cnf(c_4036,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2895,c_2242])).

cnf(c_10946,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10864,c_4036])).

cnf(c_10970,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10946])).

cnf(c_4687,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2239,c_4683])).

cnf(c_7421,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_4687])).

cnf(c_7432,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7421,c_3])).

cnf(c_7426,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_2220])).

cnf(c_7428,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7426,c_3])).

cnf(c_7422,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_4683])).

cnf(c_7431,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7422,c_3])).

cnf(c_8541,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7432,c_7428,c_7431])).

cnf(c_8542,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8541])).

cnf(c_8546,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_8542])).

cnf(c_2260,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2250])).

cnf(c_1464,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_4026,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X2
    | u1_struct_0(sK0) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1464])).

cnf(c_4027,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X0
    | u1_struct_0(sK0) != X1
    | sK3 != X2
    | v1_funct_2(X2,X1,X0) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4026])).

cnf(c_4029,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k1_xboole_0
    | u1_struct_0(sK0) != k1_xboole_0
    | sK3 != k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4027])).

cnf(c_7425,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_2896])).

cnf(c_7429,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7425,c_3])).

cnf(c_7864,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7429,c_4036])).

cnf(c_8090,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6559,c_8086])).

cnf(c_10865,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relset_1(k1_xboole_0,X1,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_4469])).

cnf(c_10978,plain,
    ( m1_subset_1(k2_zfmisc_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5894,c_10865])).

cnf(c_10983,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10978,c_4])).

cnf(c_10856,plain,
    ( r1_tarski(k1_relset_1(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_4469])).

cnf(c_3734,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2240,c_2236])).

cnf(c_10868,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10856,c_3734])).

cnf(c_10887,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10868])).

cnf(c_11052,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10983,c_10887])).

cnf(c_11057,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11052,c_4036])).

cnf(c_11194,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8090,c_9586,c_11057])).

cnf(c_11288,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8546,c_28,c_102,c_2260,c_4029,c_6350,c_7427,c_7864,c_8542,c_10970,c_11194])).

cnf(c_11290,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11288,c_9586,c_11057])).

cnf(c_11303,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11290,c_2220])).

cnf(c_11305,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11303,c_4])).

cnf(c_11318,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11305])).

cnf(c_11298,plain,
    ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11290,c_6941])).

cnf(c_11310,plain,
    ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11298,c_4])).

cnf(c_11323,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11310])).

cnf(c_11745,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(sK3,X3,u1_struct_0(sK1))
    | X3 != X1
    | u1_struct_0(sK1) != X2
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1464])).

cnf(c_11747,plain,
    ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11745])).

cnf(c_12530,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9595,c_101,c_102,c_103,c_104,c_2261,c_8906,c_9614,c_10970,c_11305,c_11318,c_11323,c_11747])).

cnf(c_12532,plain,
    ( u1_struct_0(sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12530,c_11057])).

cnf(c_11536,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11305,c_8906])).

cnf(c_11562,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11536,c_4683])).

cnf(c_12095,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_11562])).

cnf(c_12534,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12532,c_12095])).

cnf(c_11304,plain,
    ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11290,c_2219])).

cnf(c_11552,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11536,c_11304])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12534,c_11552])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.53/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/1.00  
% 3.53/1.00  ------  iProver source info
% 3.53/1.00  
% 3.53/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.53/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/1.00  git: non_committed_changes: false
% 3.53/1.00  git: last_make_outside_of_git: false
% 3.53/1.00  
% 3.53/1.00  ------ 
% 3.53/1.00  
% 3.53/1.00  ------ Input Options
% 3.53/1.00  
% 3.53/1.00  --out_options                           all
% 3.53/1.00  --tptp_safe_out                         true
% 3.53/1.00  --problem_path                          ""
% 3.53/1.00  --include_path                          ""
% 3.53/1.00  --clausifier                            res/vclausify_rel
% 3.53/1.00  --clausifier_options                    ""
% 3.53/1.00  --stdin                                 false
% 3.53/1.00  --stats_out                             all
% 3.53/1.00  
% 3.53/1.00  ------ General Options
% 3.53/1.00  
% 3.53/1.00  --fof                                   false
% 3.53/1.00  --time_out_real                         305.
% 3.53/1.00  --time_out_virtual                      -1.
% 3.53/1.00  --symbol_type_check                     false
% 3.53/1.00  --clausify_out                          false
% 3.53/1.00  --sig_cnt_out                           false
% 3.53/1.00  --trig_cnt_out                          false
% 3.53/1.00  --trig_cnt_out_tolerance                1.
% 3.53/1.00  --trig_cnt_out_sk_spl                   false
% 3.53/1.00  --abstr_cl_out                          false
% 3.53/1.00  
% 3.53/1.00  ------ Global Options
% 3.53/1.00  
% 3.53/1.00  --schedule                              default
% 3.53/1.00  --add_important_lit                     false
% 3.53/1.00  --prop_solver_per_cl                    1000
% 3.53/1.00  --min_unsat_core                        false
% 3.53/1.00  --soft_assumptions                      false
% 3.53/1.00  --soft_lemma_size                       3
% 3.53/1.00  --prop_impl_unit_size                   0
% 3.53/1.00  --prop_impl_unit                        []
% 3.53/1.00  --share_sel_clauses                     true
% 3.53/1.00  --reset_solvers                         false
% 3.53/1.00  --bc_imp_inh                            [conj_cone]
% 3.53/1.00  --conj_cone_tolerance                   3.
% 3.53/1.00  --extra_neg_conj                        none
% 3.53/1.00  --large_theory_mode                     true
% 3.53/1.00  --prolific_symb_bound                   200
% 3.53/1.00  --lt_threshold                          2000
% 3.53/1.00  --clause_weak_htbl                      true
% 3.53/1.00  --gc_record_bc_elim                     false
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing Options
% 3.53/1.00  
% 3.53/1.00  --preprocessing_flag                    true
% 3.53/1.00  --time_out_prep_mult                    0.1
% 3.53/1.00  --splitting_mode                        input
% 3.53/1.00  --splitting_grd                         true
% 3.53/1.00  --splitting_cvd                         false
% 3.53/1.00  --splitting_cvd_svl                     false
% 3.53/1.00  --splitting_nvd                         32
% 3.53/1.00  --sub_typing                            true
% 3.53/1.00  --prep_gs_sim                           true
% 3.53/1.00  --prep_unflatten                        true
% 3.53/1.00  --prep_res_sim                          true
% 3.53/1.00  --prep_upred                            true
% 3.53/1.00  --prep_sem_filter                       exhaustive
% 3.53/1.00  --prep_sem_filter_out                   false
% 3.53/1.00  --pred_elim                             true
% 3.53/1.00  --res_sim_input                         true
% 3.53/1.00  --eq_ax_congr_red                       true
% 3.53/1.00  --pure_diseq_elim                       true
% 3.53/1.00  --brand_transform                       false
% 3.53/1.00  --non_eq_to_eq                          false
% 3.53/1.00  --prep_def_merge                        true
% 3.53/1.00  --prep_def_merge_prop_impl              false
% 3.53/1.00  --prep_def_merge_mbd                    true
% 3.53/1.00  --prep_def_merge_tr_red                 false
% 3.53/1.00  --prep_def_merge_tr_cl                  false
% 3.53/1.00  --smt_preprocessing                     true
% 3.53/1.00  --smt_ac_axioms                         fast
% 3.53/1.00  --preprocessed_out                      false
% 3.53/1.00  --preprocessed_stats                    false
% 3.53/1.00  
% 3.53/1.00  ------ Abstraction refinement Options
% 3.53/1.00  
% 3.53/1.00  --abstr_ref                             []
% 3.53/1.00  --abstr_ref_prep                        false
% 3.53/1.00  --abstr_ref_until_sat                   false
% 3.53/1.00  --abstr_ref_sig_restrict                funpre
% 3.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.00  --abstr_ref_under                       []
% 3.53/1.00  
% 3.53/1.00  ------ SAT Options
% 3.53/1.00  
% 3.53/1.00  --sat_mode                              false
% 3.53/1.00  --sat_fm_restart_options                ""
% 3.53/1.00  --sat_gr_def                            false
% 3.53/1.00  --sat_epr_types                         true
% 3.53/1.00  --sat_non_cyclic_types                  false
% 3.53/1.00  --sat_finite_models                     false
% 3.53/1.00  --sat_fm_lemmas                         false
% 3.53/1.00  --sat_fm_prep                           false
% 3.53/1.00  --sat_fm_uc_incr                        true
% 3.53/1.00  --sat_out_model                         small
% 3.53/1.00  --sat_out_clauses                       false
% 3.53/1.00  
% 3.53/1.00  ------ QBF Options
% 3.53/1.00  
% 3.53/1.00  --qbf_mode                              false
% 3.53/1.00  --qbf_elim_univ                         false
% 3.53/1.00  --qbf_dom_inst                          none
% 3.53/1.00  --qbf_dom_pre_inst                      false
% 3.53/1.00  --qbf_sk_in                             false
% 3.53/1.00  --qbf_pred_elim                         true
% 3.53/1.00  --qbf_split                             512
% 3.53/1.00  
% 3.53/1.00  ------ BMC1 Options
% 3.53/1.00  
% 3.53/1.00  --bmc1_incremental                      false
% 3.53/1.00  --bmc1_axioms                           reachable_all
% 3.53/1.00  --bmc1_min_bound                        0
% 3.53/1.00  --bmc1_max_bound                        -1
% 3.53/1.00  --bmc1_max_bound_default                -1
% 3.53/1.00  --bmc1_symbol_reachability              true
% 3.53/1.00  --bmc1_property_lemmas                  false
% 3.53/1.00  --bmc1_k_induction                      false
% 3.53/1.00  --bmc1_non_equiv_states                 false
% 3.53/1.00  --bmc1_deadlock                         false
% 3.53/1.00  --bmc1_ucm                              false
% 3.53/1.00  --bmc1_add_unsat_core                   none
% 3.53/1.00  --bmc1_unsat_core_children              false
% 3.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.00  --bmc1_out_stat                         full
% 3.53/1.00  --bmc1_ground_init                      false
% 3.53/1.00  --bmc1_pre_inst_next_state              false
% 3.53/1.00  --bmc1_pre_inst_state                   false
% 3.53/1.00  --bmc1_pre_inst_reach_state             false
% 3.53/1.00  --bmc1_out_unsat_core                   false
% 3.53/1.00  --bmc1_aig_witness_out                  false
% 3.53/1.00  --bmc1_verbose                          false
% 3.53/1.00  --bmc1_dump_clauses_tptp                false
% 3.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.00  --bmc1_dump_file                        -
% 3.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.00  --bmc1_ucm_extend_mode                  1
% 3.53/1.00  --bmc1_ucm_init_mode                    2
% 3.53/1.00  --bmc1_ucm_cone_mode                    none
% 3.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.00  --bmc1_ucm_relax_model                  4
% 3.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.00  --bmc1_ucm_layered_model                none
% 3.53/1.00  --bmc1_ucm_max_lemma_size               10
% 3.53/1.00  
% 3.53/1.00  ------ AIG Options
% 3.53/1.00  
% 3.53/1.00  --aig_mode                              false
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation Options
% 3.53/1.00  
% 3.53/1.00  --instantiation_flag                    true
% 3.53/1.00  --inst_sos_flag                         true
% 3.53/1.00  --inst_sos_phase                        true
% 3.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel_side                     num_symb
% 3.53/1.00  --inst_solver_per_active                1400
% 3.53/1.00  --inst_solver_calls_frac                1.
% 3.53/1.00  --inst_passive_queue_type               priority_queues
% 3.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.00  --inst_passive_queues_freq              [25;2]
% 3.53/1.00  --inst_dismatching                      true
% 3.53/1.00  --inst_eager_unprocessed_to_passive     true
% 3.53/1.00  --inst_prop_sim_given                   true
% 3.53/1.00  --inst_prop_sim_new                     false
% 3.53/1.00  --inst_subs_new                         false
% 3.53/1.00  --inst_eq_res_simp                      false
% 3.53/1.00  --inst_subs_given                       false
% 3.53/1.00  --inst_orphan_elimination               true
% 3.53/1.00  --inst_learning_loop_flag               true
% 3.53/1.00  --inst_learning_start                   3000
% 3.53/1.00  --inst_learning_factor                  2
% 3.53/1.00  --inst_start_prop_sim_after_learn       3
% 3.53/1.00  --inst_sel_renew                        solver
% 3.53/1.00  --inst_lit_activity_flag                true
% 3.53/1.00  --inst_restr_to_given                   false
% 3.53/1.00  --inst_activity_threshold               500
% 3.53/1.00  --inst_out_proof                        true
% 3.53/1.00  
% 3.53/1.00  ------ Resolution Options
% 3.53/1.00  
% 3.53/1.00  --resolution_flag                       true
% 3.53/1.00  --res_lit_sel                           adaptive
% 3.53/1.00  --res_lit_sel_side                      none
% 3.53/1.00  --res_ordering                          kbo
% 3.53/1.00  --res_to_prop_solver                    active
% 3.53/1.00  --res_prop_simpl_new                    false
% 3.53/1.00  --res_prop_simpl_given                  true
% 3.53/1.00  --res_passive_queue_type                priority_queues
% 3.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.00  --res_passive_queues_freq               [15;5]
% 3.53/1.00  --res_forward_subs                      full
% 3.53/1.00  --res_backward_subs                     full
% 3.53/1.00  --res_forward_subs_resolution           true
% 3.53/1.00  --res_backward_subs_resolution          true
% 3.53/1.00  --res_orphan_elimination                true
% 3.53/1.00  --res_time_limit                        2.
% 3.53/1.00  --res_out_proof                         true
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Options
% 3.53/1.00  
% 3.53/1.00  --superposition_flag                    true
% 3.53/1.00  --sup_passive_queue_type                priority_queues
% 3.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.00  --demod_completeness_check              fast
% 3.53/1.00  --demod_use_ground                      true
% 3.53/1.00  --sup_to_prop_solver                    passive
% 3.53/1.00  --sup_prop_simpl_new                    true
% 3.53/1.00  --sup_prop_simpl_given                  true
% 3.53/1.00  --sup_fun_splitting                     true
% 3.53/1.00  --sup_smt_interval                      50000
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Simplification Setup
% 3.53/1.00  
% 3.53/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.53/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.53/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.53/1.00  --sup_immed_triv                        [TrivRules]
% 3.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_immed_bw_main                     []
% 3.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_input_bw                          []
% 3.53/1.00  
% 3.53/1.00  ------ Combination Options
% 3.53/1.00  
% 3.53/1.00  --comb_res_mult                         3
% 3.53/1.00  --comb_sup_mult                         2
% 3.53/1.00  --comb_inst_mult                        10
% 3.53/1.00  
% 3.53/1.00  ------ Debug Options
% 3.53/1.00  
% 3.53/1.00  --dbg_backtrace                         false
% 3.53/1.00  --dbg_dump_prop_clauses                 false
% 3.53/1.00  --dbg_dump_prop_clauses_file            -
% 3.53/1.00  --dbg_out_stat                          false
% 3.53/1.00  ------ Parsing...
% 3.53/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/1.00  ------ Proving...
% 3.53/1.00  ------ Problem Properties 
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  clauses                                 36
% 3.53/1.00  conjectures                             13
% 3.53/1.00  EPR                                     9
% 3.53/1.00  Horn                                    30
% 3.53/1.00  unary                                   15
% 3.53/1.00  binary                                  8
% 3.53/1.00  lits                                    105
% 3.53/1.00  lits eq                                 17
% 3.53/1.00  fd_pure                                 0
% 3.53/1.00  fd_pseudo                               0
% 3.53/1.00  fd_cond                                 4
% 3.53/1.00  fd_pseudo_cond                          1
% 3.53/1.00  AC symbols                              0
% 3.53/1.00  
% 3.53/1.00  ------ Schedule dynamic 5 is on 
% 3.53/1.00  
% 3.53/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ 
% 3.53/1.00  Current options:
% 3.53/1.00  ------ 
% 3.53/1.00  
% 3.53/1.00  ------ Input Options
% 3.53/1.00  
% 3.53/1.00  --out_options                           all
% 3.53/1.00  --tptp_safe_out                         true
% 3.53/1.00  --problem_path                          ""
% 3.53/1.00  --include_path                          ""
% 3.53/1.00  --clausifier                            res/vclausify_rel
% 3.53/1.00  --clausifier_options                    ""
% 3.53/1.00  --stdin                                 false
% 3.53/1.00  --stats_out                             all
% 3.53/1.00  
% 3.53/1.00  ------ General Options
% 3.53/1.00  
% 3.53/1.00  --fof                                   false
% 3.53/1.00  --time_out_real                         305.
% 3.53/1.00  --time_out_virtual                      -1.
% 3.53/1.00  --symbol_type_check                     false
% 3.53/1.00  --clausify_out                          false
% 3.53/1.00  --sig_cnt_out                           false
% 3.53/1.00  --trig_cnt_out                          false
% 3.53/1.00  --trig_cnt_out_tolerance                1.
% 3.53/1.00  --trig_cnt_out_sk_spl                   false
% 3.53/1.00  --abstr_cl_out                          false
% 3.53/1.00  
% 3.53/1.00  ------ Global Options
% 3.53/1.00  
% 3.53/1.00  --schedule                              default
% 3.53/1.00  --add_important_lit                     false
% 3.53/1.00  --prop_solver_per_cl                    1000
% 3.53/1.00  --min_unsat_core                        false
% 3.53/1.00  --soft_assumptions                      false
% 3.53/1.00  --soft_lemma_size                       3
% 3.53/1.00  --prop_impl_unit_size                   0
% 3.53/1.00  --prop_impl_unit                        []
% 3.53/1.00  --share_sel_clauses                     true
% 3.53/1.00  --reset_solvers                         false
% 3.53/1.00  --bc_imp_inh                            [conj_cone]
% 3.53/1.00  --conj_cone_tolerance                   3.
% 3.53/1.00  --extra_neg_conj                        none
% 3.53/1.00  --large_theory_mode                     true
% 3.53/1.00  --prolific_symb_bound                   200
% 3.53/1.00  --lt_threshold                          2000
% 3.53/1.00  --clause_weak_htbl                      true
% 3.53/1.00  --gc_record_bc_elim                     false
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing Options
% 3.53/1.00  
% 3.53/1.00  --preprocessing_flag                    true
% 3.53/1.00  --time_out_prep_mult                    0.1
% 3.53/1.00  --splitting_mode                        input
% 3.53/1.00  --splitting_grd                         true
% 3.53/1.00  --splitting_cvd                         false
% 3.53/1.00  --splitting_cvd_svl                     false
% 3.53/1.00  --splitting_nvd                         32
% 3.53/1.00  --sub_typing                            true
% 3.53/1.00  --prep_gs_sim                           true
% 3.53/1.00  --prep_unflatten                        true
% 3.53/1.00  --prep_res_sim                          true
% 3.53/1.00  --prep_upred                            true
% 3.53/1.00  --prep_sem_filter                       exhaustive
% 3.53/1.00  --prep_sem_filter_out                   false
% 3.53/1.00  --pred_elim                             true
% 3.53/1.00  --res_sim_input                         true
% 3.53/1.00  --eq_ax_congr_red                       true
% 3.53/1.00  --pure_diseq_elim                       true
% 3.53/1.00  --brand_transform                       false
% 3.53/1.00  --non_eq_to_eq                          false
% 3.53/1.00  --prep_def_merge                        true
% 3.53/1.00  --prep_def_merge_prop_impl              false
% 3.53/1.00  --prep_def_merge_mbd                    true
% 3.53/1.00  --prep_def_merge_tr_red                 false
% 3.53/1.00  --prep_def_merge_tr_cl                  false
% 3.53/1.00  --smt_preprocessing                     true
% 3.53/1.00  --smt_ac_axioms                         fast
% 3.53/1.00  --preprocessed_out                      false
% 3.53/1.00  --preprocessed_stats                    false
% 3.53/1.00  
% 3.53/1.00  ------ Abstraction refinement Options
% 3.53/1.00  
% 3.53/1.00  --abstr_ref                             []
% 3.53/1.00  --abstr_ref_prep                        false
% 3.53/1.00  --abstr_ref_until_sat                   false
% 3.53/1.00  --abstr_ref_sig_restrict                funpre
% 3.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/1.00  --abstr_ref_under                       []
% 3.53/1.00  
% 3.53/1.00  ------ SAT Options
% 3.53/1.00  
% 3.53/1.00  --sat_mode                              false
% 3.53/1.00  --sat_fm_restart_options                ""
% 3.53/1.00  --sat_gr_def                            false
% 3.53/1.00  --sat_epr_types                         true
% 3.53/1.00  --sat_non_cyclic_types                  false
% 3.53/1.00  --sat_finite_models                     false
% 3.53/1.00  --sat_fm_lemmas                         false
% 3.53/1.00  --sat_fm_prep                           false
% 3.53/1.00  --sat_fm_uc_incr                        true
% 3.53/1.00  --sat_out_model                         small
% 3.53/1.00  --sat_out_clauses                       false
% 3.53/1.00  
% 3.53/1.00  ------ QBF Options
% 3.53/1.00  
% 3.53/1.00  --qbf_mode                              false
% 3.53/1.00  --qbf_elim_univ                         false
% 3.53/1.00  --qbf_dom_inst                          none
% 3.53/1.00  --qbf_dom_pre_inst                      false
% 3.53/1.00  --qbf_sk_in                             false
% 3.53/1.00  --qbf_pred_elim                         true
% 3.53/1.00  --qbf_split                             512
% 3.53/1.00  
% 3.53/1.00  ------ BMC1 Options
% 3.53/1.00  
% 3.53/1.00  --bmc1_incremental                      false
% 3.53/1.00  --bmc1_axioms                           reachable_all
% 3.53/1.00  --bmc1_min_bound                        0
% 3.53/1.00  --bmc1_max_bound                        -1
% 3.53/1.00  --bmc1_max_bound_default                -1
% 3.53/1.00  --bmc1_symbol_reachability              true
% 3.53/1.00  --bmc1_property_lemmas                  false
% 3.53/1.00  --bmc1_k_induction                      false
% 3.53/1.00  --bmc1_non_equiv_states                 false
% 3.53/1.00  --bmc1_deadlock                         false
% 3.53/1.00  --bmc1_ucm                              false
% 3.53/1.00  --bmc1_add_unsat_core                   none
% 3.53/1.00  --bmc1_unsat_core_children              false
% 3.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/1.00  --bmc1_out_stat                         full
% 3.53/1.00  --bmc1_ground_init                      false
% 3.53/1.00  --bmc1_pre_inst_next_state              false
% 3.53/1.00  --bmc1_pre_inst_state                   false
% 3.53/1.00  --bmc1_pre_inst_reach_state             false
% 3.53/1.00  --bmc1_out_unsat_core                   false
% 3.53/1.00  --bmc1_aig_witness_out                  false
% 3.53/1.00  --bmc1_verbose                          false
% 3.53/1.00  --bmc1_dump_clauses_tptp                false
% 3.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.53/1.00  --bmc1_dump_file                        -
% 3.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.53/1.00  --bmc1_ucm_extend_mode                  1
% 3.53/1.00  --bmc1_ucm_init_mode                    2
% 3.53/1.00  --bmc1_ucm_cone_mode                    none
% 3.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.53/1.00  --bmc1_ucm_relax_model                  4
% 3.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/1.00  --bmc1_ucm_layered_model                none
% 3.53/1.00  --bmc1_ucm_max_lemma_size               10
% 3.53/1.00  
% 3.53/1.00  ------ AIG Options
% 3.53/1.00  
% 3.53/1.00  --aig_mode                              false
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation Options
% 3.53/1.00  
% 3.53/1.00  --instantiation_flag                    true
% 3.53/1.00  --inst_sos_flag                         true
% 3.53/1.00  --inst_sos_phase                        true
% 3.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/1.00  --inst_lit_sel_side                     none
% 3.53/1.00  --inst_solver_per_active                1400
% 3.53/1.00  --inst_solver_calls_frac                1.
% 3.53/1.00  --inst_passive_queue_type               priority_queues
% 3.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/1.00  --inst_passive_queues_freq              [25;2]
% 3.53/1.00  --inst_dismatching                      true
% 3.53/1.00  --inst_eager_unprocessed_to_passive     true
% 3.53/1.00  --inst_prop_sim_given                   true
% 3.53/1.00  --inst_prop_sim_new                     false
% 3.53/1.00  --inst_subs_new                         false
% 3.53/1.00  --inst_eq_res_simp                      false
% 3.53/1.00  --inst_subs_given                       false
% 3.53/1.00  --inst_orphan_elimination               true
% 3.53/1.00  --inst_learning_loop_flag               true
% 3.53/1.00  --inst_learning_start                   3000
% 3.53/1.00  --inst_learning_factor                  2
% 3.53/1.00  --inst_start_prop_sim_after_learn       3
% 3.53/1.00  --inst_sel_renew                        solver
% 3.53/1.00  --inst_lit_activity_flag                true
% 3.53/1.00  --inst_restr_to_given                   false
% 3.53/1.00  --inst_activity_threshold               500
% 3.53/1.00  --inst_out_proof                        true
% 3.53/1.00  
% 3.53/1.00  ------ Resolution Options
% 3.53/1.00  
% 3.53/1.00  --resolution_flag                       false
% 3.53/1.00  --res_lit_sel                           adaptive
% 3.53/1.00  --res_lit_sel_side                      none
% 3.53/1.00  --res_ordering                          kbo
% 3.53/1.00  --res_to_prop_solver                    active
% 3.53/1.00  --res_prop_simpl_new                    false
% 3.53/1.00  --res_prop_simpl_given                  true
% 3.53/1.00  --res_passive_queue_type                priority_queues
% 3.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/1.00  --res_passive_queues_freq               [15;5]
% 3.53/1.00  --res_forward_subs                      full
% 3.53/1.00  --res_backward_subs                     full
% 3.53/1.00  --res_forward_subs_resolution           true
% 3.53/1.00  --res_backward_subs_resolution          true
% 3.53/1.00  --res_orphan_elimination                true
% 3.53/1.00  --res_time_limit                        2.
% 3.53/1.00  --res_out_proof                         true
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Options
% 3.53/1.00  
% 3.53/1.00  --superposition_flag                    true
% 3.53/1.00  --sup_passive_queue_type                priority_queues
% 3.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.53/1.00  --demod_completeness_check              fast
% 3.53/1.00  --demod_use_ground                      true
% 3.53/1.00  --sup_to_prop_solver                    passive
% 3.53/1.00  --sup_prop_simpl_new                    true
% 3.53/1.00  --sup_prop_simpl_given                  true
% 3.53/1.00  --sup_fun_splitting                     true
% 3.53/1.00  --sup_smt_interval                      50000
% 3.53/1.00  
% 3.53/1.00  ------ Superposition Simplification Setup
% 3.53/1.00  
% 3.53/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.53/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.53/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.53/1.00  --sup_immed_triv                        [TrivRules]
% 3.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_immed_bw_main                     []
% 3.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/1.00  --sup_input_bw                          []
% 3.53/1.00  
% 3.53/1.00  ------ Combination Options
% 3.53/1.00  
% 3.53/1.00  --comb_res_mult                         3
% 3.53/1.00  --comb_sup_mult                         2
% 3.53/1.00  --comb_inst_mult                        10
% 3.53/1.00  
% 3.53/1.00  ------ Debug Options
% 3.53/1.00  
% 3.53/1.00  --dbg_backtrace                         false
% 3.53/1.00  --dbg_dump_prop_clauses                 false
% 3.53/1.00  --dbg_dump_prop_clauses_file            -
% 3.53/1.00  --dbg_out_stat                          false
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ Proving...
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS status Theorem for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  fof(f14,conjecture,(
% 3.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f15,negated_conjecture,(
% 3.53/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.53/1.00    inference(negated_conjecture,[],[f14])).
% 3.53/1.00  
% 3.53/1.00  fof(f31,plain,(
% 3.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f15])).
% 3.53/1.00  
% 3.53/1.00  fof(f32,plain,(
% 3.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.53/1.00    inference(flattening,[],[f31])).
% 3.53/1.00  
% 3.53/1.00  fof(f41,plain,(
% 3.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.53/1.00    inference(nnf_transformation,[],[f32])).
% 3.53/1.00  
% 3.53/1.00  fof(f42,plain,(
% 3.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.53/1.00    inference(flattening,[],[f41])).
% 3.53/1.00  
% 3.53/1.00  fof(f46,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK3 = X2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK3))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f45,plain,(
% 3.53/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK2,X0,X1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f44,plain,(
% 3.53/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,X0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,X0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f43,plain,(
% 3.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f47,plain,(
% 3.53/1.00    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f46,f45,f44,f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f81,plain,(
% 3.53/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f8,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f21,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f8])).
% 3.53/1.00  
% 3.53/1.00  fof(f22,plain,(
% 3.53/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(flattening,[],[f21])).
% 3.53/1.00  
% 3.53/1.00  fof(f38,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(nnf_transformation,[],[f22])).
% 3.53/1.00  
% 3.53/1.00  fof(f59,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f38])).
% 3.53/1.00  
% 3.53/1.00  fof(f7,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f20,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f7])).
% 3.53/1.00  
% 3.53/1.00  fof(f58,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f20])).
% 3.53/1.00  
% 3.53/1.00  fof(f80,plain,(
% 3.53/1.00    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f4,axiom,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f37,plain,(
% 3.53/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.53/1.00    inference(nnf_transformation,[],[f4])).
% 3.53/1.00  
% 3.53/1.00  fof(f55,plain,(
% 3.53/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f37])).
% 3.53/1.00  
% 3.53/1.00  fof(f1,axiom,(
% 3.53/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f33,plain,(
% 3.53/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/1.00    inference(nnf_transformation,[],[f1])).
% 3.53/1.00  
% 3.53/1.00  fof(f34,plain,(
% 3.53/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/1.00    inference(flattening,[],[f33])).
% 3.53/1.00  
% 3.53/1.00  fof(f50,plain,(
% 3.53/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f34])).
% 3.53/1.00  
% 3.53/1.00  fof(f2,axiom,(
% 3.53/1.00    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f35,plain,(
% 3.53/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.53/1.00    inference(nnf_transformation,[],[f2])).
% 3.53/1.00  
% 3.53/1.00  fof(f36,plain,(
% 3.53/1.00    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.53/1.00    inference(flattening,[],[f35])).
% 3.53/1.00  
% 3.53/1.00  fof(f53,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.53/1.00    inference(cnf_transformation,[],[f36])).
% 3.53/1.00  
% 3.53/1.00  fof(f87,plain,(
% 3.53/1.00    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.53/1.00    inference(equality_resolution,[],[f53])).
% 3.53/1.00  
% 3.53/1.00  fof(f3,axiom,(
% 3.53/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f54,plain,(
% 3.53/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f3])).
% 3.53/1.00  
% 3.53/1.00  fof(f49,plain,(
% 3.53/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.53/1.00    inference(cnf_transformation,[],[f34])).
% 3.53/1.00  
% 3.53/1.00  fof(f85,plain,(
% 3.53/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.53/1.00    inference(equality_resolution,[],[f49])).
% 3.53/1.00  
% 3.53/1.00  fof(f56,plain,(
% 3.53/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f37])).
% 3.53/1.00  
% 3.53/1.00  fof(f78,plain,(
% 3.53/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f82,plain,(
% 3.53/1.00    sK2 = sK3),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f77,plain,(
% 3.53/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f12,axiom,(
% 3.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f27,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f12])).
% 3.53/1.00  
% 3.53/1.00  fof(f28,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.53/1.00    inference(flattening,[],[f27])).
% 3.53/1.00  
% 3.53/1.00  fof(f39,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.53/1.00    inference(nnf_transformation,[],[f28])).
% 3.53/1.00  
% 3.53/1.00  fof(f68,plain,(
% 3.53/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f39])).
% 3.53/1.00  
% 3.53/1.00  fof(f95,plain,(
% 3.53/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f68])).
% 3.53/1.00  
% 3.53/1.00  fof(f72,plain,(
% 3.53/1.00    v2_pre_topc(sK0)),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f73,plain,(
% 3.53/1.00    l1_pre_topc(sK0)),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f74,plain,(
% 3.53/1.00    v2_pre_topc(sK1)),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f75,plain,(
% 3.53/1.00    l1_pre_topc(sK1)),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f79,plain,(
% 3.53/1.00    v1_funct_1(sK3)),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f83,plain,(
% 3.53/1.00    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f84,plain,(
% 3.53/1.00    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 3.53/1.00    inference(cnf_transformation,[],[f47])).
% 3.53/1.00  
% 3.53/1.00  fof(f11,axiom,(
% 3.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f16,plain,(
% 3.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.53/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.53/1.00  
% 3.53/1.00  fof(f25,plain,(
% 3.53/1.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f16])).
% 3.53/1.00  
% 3.53/1.00  fof(f26,plain,(
% 3.53/1.00    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.53/1.00    inference(flattening,[],[f25])).
% 3.53/1.00  
% 3.53/1.00  fof(f67,plain,(
% 3.53/1.00    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f26])).
% 3.53/1.00  
% 3.53/1.00  fof(f9,axiom,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f17,plain,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.53/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.53/1.00  
% 3.53/1.00  fof(f23,plain,(
% 3.53/1.00    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.53/1.00    inference(ennf_transformation,[],[f17])).
% 3.53/1.00  
% 3.53/1.00  fof(f65,plain,(
% 3.53/1.00    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f23])).
% 3.53/1.00  
% 3.53/1.00  fof(f10,axiom,(
% 3.53/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f24,plain,(
% 3.53/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f10])).
% 3.53/1.00  
% 3.53/1.00  fof(f66,plain,(
% 3.53/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f24])).
% 3.53/1.00  
% 3.53/1.00  fof(f13,axiom,(
% 3.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f29,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f13])).
% 3.53/1.00  
% 3.53/1.00  fof(f30,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.53/1.00    inference(flattening,[],[f29])).
% 3.53/1.00  
% 3.53/1.00  fof(f40,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.53/1.00    inference(nnf_transformation,[],[f30])).
% 3.53/1.00  
% 3.53/1.00  fof(f71,plain,(
% 3.53/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f40])).
% 3.53/1.00  
% 3.53/1.00  fof(f96,plain,(
% 3.53/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f71])).
% 3.53/1.00  
% 3.53/1.00  fof(f69,plain,(
% 3.53/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f39])).
% 3.53/1.00  
% 3.53/1.00  fof(f94,plain,(
% 3.53/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f69])).
% 3.53/1.00  
% 3.53/1.00  fof(f70,plain,(
% 3.53/1.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f40])).
% 3.53/1.00  
% 3.53/1.00  fof(f97,plain,(
% 3.53/1.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f70])).
% 3.53/1.00  
% 3.53/1.00  fof(f51,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.53/1.00    inference(cnf_transformation,[],[f36])).
% 3.53/1.00  
% 3.53/1.00  fof(f52,plain,(
% 3.53/1.00    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.53/1.00    inference(cnf_transformation,[],[f36])).
% 3.53/1.00  
% 3.53/1.00  fof(f88,plain,(
% 3.53/1.00    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.53/1.00    inference(equality_resolution,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f62,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f38])).
% 3.53/1.00  
% 3.53/1.00  fof(f92,plain,(
% 3.53/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.53/1.00    inference(equality_resolution,[],[f62])).
% 3.53/1.00  
% 3.53/1.00  fof(f63,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f38])).
% 3.53/1.00  
% 3.53/1.00  fof(f91,plain,(
% 3.53/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.53/1.00    inference(equality_resolution,[],[f63])).
% 3.53/1.00  
% 3.53/1.00  fof(f6,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.53/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f19,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.53/1.00    inference(ennf_transformation,[],[f6])).
% 3.53/1.00  
% 3.53/1.00  fof(f57,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f19])).
% 3.53/1.00  
% 3.53/1.00  cnf(c_27,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2220,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_16,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.53/1.00      | k1_xboole_0 = X2 ),
% 3.53/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2230,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.53/1.00      | k1_xboole_0 = X1
% 3.53/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6336,plain,
% 3.53/1.00      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2220,c_2230]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2236,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.53/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3736,plain,
% 3.53/1.00      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2220,c_2236]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6343,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_6336,c_3736]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_28,negated_conjecture,
% 3.53/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6350,plain,
% 3.53/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6343]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7393,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_6343,c_28,c_6350]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7394,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_7393]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2238,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.53/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2896,plain,
% 3.53/1.00      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2220,c_2238]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_0,plain,
% 3.53/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.53/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2242,plain,
% 3.53/1.00      ( X0 = X1
% 3.53/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.53/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4038,plain,
% 3.53/1.00      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 3.53/1.00      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK3) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2896,c_2242]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7423,plain,
% 3.53/1.00      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0),sK3) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7394,c_4038]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3,plain,
% 3.53/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7430,plain,
% 3.53/1.00      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7423,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2564,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2565,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 3.53/1.00      | r1_tarski(X0,sK3) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2564]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2567,plain,
% 3.53/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 3.53/1.00      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_2565]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6,plain,
% 3.53/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3103,plain,
% 3.53/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3104,plain,
% 3.53/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3103]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8562,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_7430,c_2567,c_3104]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8563,plain,
% 3.53/1.00      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = sK3
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_8562]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1,plain,
% 3.53/1.00      ( r1_tarski(X0,X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2241,plain,
% 3.53/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2239,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.53/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3735,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.53/1.00      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2239,c_2236]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5894,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2241,c_3735]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8568,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_8563,c_5894]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8581,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_8568,c_3736]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8902,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | k1_relat_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7394,c_8581]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8904,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_8902,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9049,plain,
% 3.53/1.00      ( k1_relset_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK3) = k1_relat_1(sK3)
% 3.53/1.00      | k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_8904,c_3736]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2219,plain,
% 3.53/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9053,plain,
% 3.53/1.00      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
% 3.53/1.00      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_8904,c_2219]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_30,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2217,plain,
% 3.53/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_26,negated_conjecture,
% 3.53/1.00      ( sK2 = sK3 ),
% 3.53/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2245,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2217,c_26]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6337,plain,
% 3.53/1.00      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = u1_struct_0(sK0)
% 3.53/1.00      | u1_struct_0(sK1) = k1_xboole_0
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2245,c_2230]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3737,plain,
% 3.53/1.00      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2245,c_2236]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6342,plain,
% 3.53/1.00      ( u1_struct_0(sK1) = k1_xboole_0
% 3.53/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_6337,c_3737]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_31,negated_conjecture,
% 3.53/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2216,plain,
% 3.53/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2244,plain,
% 3.53/1.00      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2216,c_26]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6558,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | u1_struct_0(sK1) = k1_xboole_0 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_6342,c_2244]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6559,plain,
% 3.53/1.00      ( u1_struct_0(sK1) = k1_xboole_0
% 3.53/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_6558]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2897,plain,
% 3.53/1.00      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2245,c_2238]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4039,plain,
% 3.53/1.00      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 3.53/1.00      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK3) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2897,c_2242]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6580,plain,
% 3.53/1.00      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 3.53/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),sK3) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_6559,c_4039]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6600,plain,
% 3.53/1.00      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 3.53/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_6580,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7193,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3 ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_6600,c_2567,c_3104]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7194,plain,
% 3.53/1.00      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK3
% 3.53/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_7193]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7197,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7194,c_5894]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7204,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_7197,c_3737]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7368,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | k1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_6559,c_7204]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7369,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7368,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9052,plain,
% 3.53/1.00      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_8904,c_2220]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_21,plain,
% 3.53/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 3.53/1.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.53/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.53/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | ~ v2_pre_topc(X1)
% 3.53/1.00      | ~ v2_pre_topc(X2)
% 3.53/1.00      | ~ l1_pre_topc(X1)
% 3.53/1.00      | ~ l1_pre_topc(X2) ),
% 3.53/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2225,plain,
% 3.53/1.00      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.53/1.00      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 3.53/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.53/1.00      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 3.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 3.53/1.00      | v1_funct_1(X0) != iProver_top
% 3.53/1.00      | v2_pre_topc(X1) != iProver_top
% 3.53/1.00      | v2_pre_topc(X2) != iProver_top
% 3.53/1.00      | l1_pre_topc(X1) != iProver_top
% 3.53/1.00      | l1_pre_topc(X2) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4415,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2220,c_2225]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_36,negated_conjecture,
% 3.53/1.00      ( v2_pre_topc(sK0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_37,plain,
% 3.53/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_35,negated_conjecture,
% 3.53/1.00      ( l1_pre_topc(sK0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_38,plain,
% 3.53/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_34,negated_conjecture,
% 3.53/1.00      ( v2_pre_topc(sK1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_39,plain,
% 3.53/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_33,negated_conjecture,
% 3.53/1.00      ( l1_pre_topc(sK1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_40,plain,
% 3.53/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_29,negated_conjecture,
% 3.53/1.00      ( v1_funct_1(sK3) ),
% 3.53/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_44,plain,
% 3.53/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_45,plain,
% 3.53/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_46,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_25,negated_conjecture,
% 3.53/1.00      ( v5_pre_topc(sK2,sK0,sK1)
% 3.53/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2221,plain,
% 3.53/1.00      ( v5_pre_topc(sK2,sK0,sK1) = iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2247,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2221,c_26]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_24,negated_conjecture,
% 3.53/1.00      ( ~ v5_pre_topc(sK2,sK0,sK1)
% 3.53/1.00      | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2222,plain,
% 3.53/1.00      ( v5_pre_topc(sK2,sK0,sK1) != iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2248,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,sK0,sK1) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2222,c_26]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_19,plain,
% 3.53/1.00      ( ~ v2_pre_topc(X0)
% 3.53/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.53/1.00      | ~ l1_pre_topc(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2392,plain,
% 3.53/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.53/1.00      | ~ v2_pre_topc(sK1)
% 3.53/1.00      | ~ l1_pre_topc(sK1) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2393,plain,
% 3.53/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2392]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.53/1.00      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2503,plain,
% 3.53/1.00      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.53/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2504,plain,
% 3.53/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2503]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_18,plain,
% 3.53/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.53/1.00      | ~ l1_pre_topc(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2655,plain,
% 3.53/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 3.53/1.00      | ~ l1_pre_topc(sK1) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2656,plain,
% 3.53/1.00      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2655]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_22,plain,
% 3.53/1.00      ( v5_pre_topc(X0,X1,X2)
% 3.53/1.00      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.53/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.53/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | ~ v2_pre_topc(X1)
% 3.53/1.00      | ~ v2_pre_topc(X2)
% 3.53/1.00      | ~ l1_pre_topc(X1)
% 3.53/1.00      | ~ l1_pre_topc(X2) ),
% 3.53/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2542,plain,
% 3.53/1.00      ( ~ v5_pre_topc(sK3,X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.53/1.00      | v5_pre_topc(sK3,X0,sK1)
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 3.53/1.00      | ~ v1_funct_1(sK3)
% 3.53/1.00      | ~ v2_pre_topc(X0)
% 3.53/1.00      | ~ v2_pre_topc(sK1)
% 3.53/1.00      | ~ l1_pre_topc(X0)
% 3.53/1.00      | ~ l1_pre_topc(sK1) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3023,plain,
% 3.53/1.00      ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.53/1.00      | v5_pre_topc(sK3,sK0,sK1)
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.53/1.00      | ~ v1_funct_1(sK3)
% 3.53/1.00      | ~ v2_pre_topc(sK1)
% 3.53/1.00      | ~ v2_pre_topc(sK0)
% 3.53/1.00      | ~ l1_pre_topc(sK1)
% 3.53/1.00      | ~ l1_pre_topc(sK0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_2542]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3024,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3023]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_20,plain,
% 3.53/1.00      ( v5_pre_topc(X0,X1,X2)
% 3.53/1.00      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.53/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.53/1.00      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | ~ v2_pre_topc(X1)
% 3.53/1.00      | ~ v2_pre_topc(X2)
% 3.53/1.00      | ~ l1_pre_topc(X1)
% 3.53/1.00      | ~ l1_pre_topc(X2) ),
% 3.53/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2770,plain,
% 3.53/1.00      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
% 3.53/1.00      | v5_pre_topc(sK3,sK0,X0)
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 3.53/1.00      | ~ v1_funct_1(sK3)
% 3.53/1.00      | ~ v2_pre_topc(X0)
% 3.53/1.00      | ~ v2_pre_topc(sK0)
% 3.53/1.00      | ~ l1_pre_topc(X0)
% 3.53/1.00      | ~ l1_pre_topc(sK0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3056,plain,
% 3.53/1.00      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.53/1.00      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.53/1.00      | ~ v1_funct_1(sK3)
% 3.53/1.00      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.53/1.00      | ~ v2_pre_topc(sK0)
% 3.53/1.00      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.53/1.00      | ~ l1_pre_topc(sK0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_2770]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3057,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3056]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_23,plain,
% 3.53/1.00      ( ~ v5_pre_topc(X0,X1,X2)
% 3.53/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.53/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.53/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.53/1.00      | ~ v1_funct_1(X0)
% 3.53/1.00      | ~ v2_pre_topc(X1)
% 3.53/1.00      | ~ v2_pre_topc(X2)
% 3.53/1.00      | ~ l1_pre_topc(X1)
% 3.53/1.00      | ~ l1_pre_topc(X2) ),
% 3.53/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2980,plain,
% 3.53/1.00      ( ~ v5_pre_topc(sK3,sK0,X0)
% 3.53/1.00      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
% 3.53/1.00      | ~ v1_funct_1(sK3)
% 3.53/1.00      | ~ v2_pre_topc(X0)
% 3.53/1.00      | ~ v2_pre_topc(sK0)
% 3.53/1.00      | ~ l1_pre_topc(X0)
% 3.53/1.00      | ~ l1_pre_topc(sK0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4421,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 3.53/1.00      | ~ v5_pre_topc(sK3,sK0,sK1)
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.53/1.00      | ~ v1_funct_1(sK3)
% 3.53/1.00      | ~ v2_pre_topc(sK1)
% 3.53/1.00      | ~ v2_pre_topc(sK0)
% 3.53/1.00      | ~ l1_pre_topc(sK1)
% 3.53/1.00      | ~ l1_pre_topc(sK0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_2980]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4422,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_4421]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4679,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_4415,c_37,c_38,c_39,c_40,c_44,c_45,c_46,c_2247,c_2245,
% 3.53/1.00                 c_2244,c_2248,c_2393,c_2504,c_2656,c_3024,c_3057,c_4422]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4680,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_4679]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4683,plain,
% 3.53/1.00      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_4680,c_37,c_38,c_39,c_40,c_44,c_45,c_46,c_2247,c_2245,
% 3.53/1.00                 c_2244,c_2393,c_2504,c_2656,c_3057,c_4422]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7775,plain,
% 3.53/1.00      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7369,c_4683]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9506,plain,
% 3.53/1.00      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_9052,c_7775]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9582,plain,
% 3.53/1.00      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
% 3.53/1.00      | v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7369,c_9506]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9586,plain,
% 3.53/1.00      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_9049,c_9053,c_9582]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2224,plain,
% 3.53/1.00      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 3.53/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 3.53/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.53/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.53/1.00      | v1_funct_1(X0) != iProver_top
% 3.53/1.00      | v2_pre_topc(X1) != iProver_top
% 3.53/1.00      | v2_pre_topc(X2) != iProver_top
% 3.53/1.00      | l1_pre_topc(X1) != iProver_top
% 3.53/1.00      | l1_pre_topc(X2) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3727,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.53/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2220,c_2224]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2377,plain,
% 3.53/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 3.53/1.00      | ~ v2_pre_topc(sK0)
% 3.53/1.00      | ~ l1_pre_topc(sK0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2378,plain,
% 3.53/1.00      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 3.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2377]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2491,plain,
% 3.53/1.00      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.53/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2492,plain,
% 3.53/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.53/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2491]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2644,plain,
% 3.53/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.53/1.00      | ~ l1_pre_topc(sK0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2645,plain,
% 3.53/1.00      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2644]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2223,plain,
% 3.53/1.00      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.53/1.00      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 3.53/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.53/1.00      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.53/1.00      | v1_funct_1(X0) != iProver_top
% 3.53/1.00      | v2_pre_topc(X1) != iProver_top
% 3.53/1.00      | v2_pre_topc(X2) != iProver_top
% 3.53/1.00      | l1_pre_topc(X1) != iProver_top
% 3.53/1.00      | l1_pre_topc(X2) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3094,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.53/1.00      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2220,c_2223]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3047,plain,
% 3.53/1.00      ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.53/1.00      | v5_pre_topc(sK3,sK0,sK1)
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.53/1.00      | ~ v1_funct_1(sK3)
% 3.53/1.00      | ~ v2_pre_topc(sK1)
% 3.53/1.00      | ~ v2_pre_topc(sK0)
% 3.53/1.00      | ~ l1_pre_topc(sK1)
% 3.53/1.00      | ~ l1_pre_topc(sK0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_2770]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3048,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3047]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3269,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_3094,c_37,c_38,c_39,c_40,c_44,c_45,c_2245,c_2244,
% 3.53/1.00                 c_2248,c_2378,c_2492,c_2645,c_3048]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3270,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_3269]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4086,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_3727,c_37,c_38,c_39,c_40,c_44,c_45,c_2245,c_2244,
% 3.53/1.00                 c_2248,c_2378,c_2492,c_2645,c_3048,c_3094]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4087,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_4086]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6582,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_6559,c_4087]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4090,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,sK0,sK1) = iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2247,c_4087]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2964,plain,
% 3.53/1.00      ( ~ v5_pre_topc(sK3,X0,sK1)
% 3.53/1.00      | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(sK1))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK1))))
% 3.53/1.00      | ~ v1_funct_1(sK3)
% 3.53/1.00      | ~ v2_pre_topc(X0)
% 3.53/1.00      | ~ v2_pre_topc(sK1)
% 3.53/1.00      | ~ l1_pre_topc(X0)
% 3.53/1.00      | ~ l1_pre_topc(sK1) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4398,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
% 3.53/1.00      | ~ v5_pre_topc(sK3,sK0,sK1)
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
% 3.53/1.00      | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.53/1.00      | ~ v1_funct_1(sK3)
% 3.53/1.00      | ~ v2_pre_topc(sK1)
% 3.53/1.00      | ~ v2_pre_topc(sK0)
% 3.53/1.00      | ~ l1_pre_topc(sK1)
% 3.53/1.00      | ~ l1_pre_topc(sK0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_2964]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4399,plain,
% 3.53/1.00      ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = iProver_top
% 3.53/1.00      | v5_pre_topc(sK3,sK0,sK1) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | v1_funct_1(sK3) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_4398]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6941,plain,
% 3.53/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_6582,c_37,c_38,c_39,c_40,c_44,c_2245,c_2244,c_3270,
% 3.53/1.00                 c_4090,c_4399]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6946,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_6559,c_6941]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6947,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_6946,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6593,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_6559,c_2245]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6595,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_6593,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8085,plain,
% 3.53/1.00      ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | u1_struct_0(sK0) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_6947,c_6595]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8086,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_8085]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9595,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_9586,c_8086]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_101,plain,
% 3.53/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_100,plain,
% 3.53/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_102,plain,
% 3.53/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_100]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5,plain,
% 3.53/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.53/1.00      | k1_xboole_0 = X1
% 3.53/1.00      | k1_xboole_0 = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_103,plain,
% 3.53/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.53/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4,plain,
% 3.53/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_104,plain,
% 3.53/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_13,plain,
% 3.53/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.53/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2233,plain,
% 3.53/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 3.53/1.00      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 3.53/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2250,plain,
% 3.53/1.00      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 3.53/1.00      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 3.53/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2233,c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2259,plain,
% 3.53/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 3.53/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.53/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2250]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2261,plain,
% 3.53/1.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.53/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.53/1.00      | k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_2259]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7427,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7394,c_2219]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_12,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.53/1.00      | k1_xboole_0 = X1
% 3.53/1.00      | k1_xboole_0 = X0 ),
% 3.53/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2234,plain,
% 3.53/1.00      ( k1_xboole_0 = X0
% 3.53/1.00      | k1_xboole_0 = X1
% 3.53/1.00      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 3.53/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2251,plain,
% 3.53/1.00      ( k1_xboole_0 = X0
% 3.53/1.00      | k1_xboole_0 = X1
% 3.53/1.00      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 3.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_2234,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7614,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0
% 3.53/1.00      | sK3 = k1_xboole_0
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7427,c_2251]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2578,plain,
% 3.53/1.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2579,plain,
% 3.53/1.00      ( sK3 = X0
% 3.53/1.00      | r1_tarski(X0,sK3) != iProver_top
% 3.53/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2578]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2581,plain,
% 3.53/1.00      ( sK3 = k1_xboole_0
% 3.53/1.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.53/1.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_2579]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8368,plain,
% 3.53/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8369,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.53/1.00      | r1_tarski(sK3,X0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_8368]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8371,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.53/1.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_8369]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8906,plain,
% 3.53/1.00      ( sK3 = k1_xboole_0
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_7614,c_2567,c_2581,c_3104,c_8371]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9614,plain,
% 3.53/1.00      ( u1_struct_0(sK1) = k1_xboole_0
% 3.53/1.00      | u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_9586,c_6559]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.53/1.00      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2237,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.53/1.00      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4469,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.53/1.00      | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2237,c_2238]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10864,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.53/1.00      | r1_tarski(k1_relset_1(X1,k1_xboole_0,X0),X1) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3,c_4469]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2240,plain,
% 3.53/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2895,plain,
% 3.53/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2240,c_2238]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4036,plain,
% 3.53/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2895,c_2242]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10946,plain,
% 3.53/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0
% 3.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_10864,c_4036]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10970,plain,
% 3.53/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 3.53/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_10946]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4687,plain,
% 3.53/1.00      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2239,c_4683]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7421,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7394,c_4687]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7432,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7421,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7426,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7394,c_2220]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7428,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7426,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7422,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7394,c_4683]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7431,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7422,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8541,plain,
% 3.53/1.00      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_7432,c_7428,c_7431]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8542,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_8541]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8546,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7394,c_8542]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2260,plain,
% 3.53/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.53/1.00      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 3.53/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_2250]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1464,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | v1_funct_2(X3,X4,X5)
% 3.53/1.00      | X3 != X0
% 3.53/1.00      | X4 != X1
% 3.53/1.00      | X5 != X2 ),
% 3.53/1.00      theory(equality) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4026,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
% 3.53/1.00      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X2
% 3.53/1.00      | u1_struct_0(sK0) != X1
% 3.53/1.00      | sK3 != X0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_1464]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4027,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != X0
% 3.53/1.00      | u1_struct_0(sK0) != X1
% 3.53/1.00      | sK3 != X2
% 3.53/1.00      | v1_funct_2(X2,X1,X0) != iProver_top
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_4026]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4029,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != k1_xboole_0
% 3.53/1.00      | u1_struct_0(sK0) != k1_xboole_0
% 3.53/1.00      | sK3 != k1_xboole_0
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top
% 3.53/1.00      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_4027]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7425,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7394,c_2896]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7429,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_7425,c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7864,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3)
% 3.53/1.00      | sK3 = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_7429,c_4036]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8090,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(sK3)
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_6559,c_8086]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10865,plain,
% 3.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.53/1.00      | r1_tarski(k1_relset_1(k1_xboole_0,X1,X0),k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_4,c_4469]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10978,plain,
% 3.53/1.00      ( m1_subset_1(k2_zfmisc_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.53/1.00      | r1_tarski(k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_5894,c_10865]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10983,plain,
% 3.53/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.53/1.00      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_10978,c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10856,plain,
% 3.53/1.00      ( r1_tarski(k1_relset_1(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2240,c_4469]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3734,plain,
% 3.53/1.00      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2240,c_2236]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10868,plain,
% 3.53/1.00      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_10856,c_3734]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10887,plain,
% 3.53/1.00      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_10868]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11052,plain,
% 3.53/1.00      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_10983,c_10887]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11057,plain,
% 3.53/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_11052,c_4036]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11194,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_xboole_0
% 3.53/1.00      | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_8090,c_9586,c_11057]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11288,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK3) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_8546,c_28,c_102,c_2260,c_4029,c_6350,c_7427,c_7864,
% 3.53/1.00                 c_8542,c_10970,c_11194]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11290,plain,
% 3.53/1.00      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_xboole_0 ),
% 3.53/1.00      inference(light_normalisation,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_11288,c_9586,c_11057]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11303,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_11290,c_2220]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11305,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_11303,c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11318,plain,
% 3.53/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
% 3.53/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_11305]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11298,plain,
% 3.53/1.00      ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_11290,c_6941]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11310,plain,
% 3.53/1.00      ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_11298,c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11323,plain,
% 3.53/1.00      ( ~ v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1))
% 3.53/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
% 3.53/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_11310]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11745,plain,
% 3.53/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.53/1.00      | v1_funct_2(sK3,X3,u1_struct_0(sK1))
% 3.53/1.00      | X3 != X1
% 3.53/1.00      | u1_struct_0(sK1) != X2
% 3.53/1.00      | sK3 != X0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_1464]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11747,plain,
% 3.53/1.00      ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(sK1))
% 3.53/1.00      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 3.53/1.00      | u1_struct_0(sK1) != k1_xboole_0
% 3.53/1.00      | sK3 != k1_xboole_0
% 3.53/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_11745]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_12530,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_9595,c_101,c_102,c_103,c_104,c_2261,c_8906,c_9614,
% 3.53/1.00                 c_10970,c_11305,c_11318,c_11323,c_11747]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_12532,plain,
% 3.53/1.00      ( u1_struct_0(sK0) = k1_xboole_0 ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_12530,c_11057]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11536,plain,
% 3.53/1.00      ( sK3 = k1_xboole_0 ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_11305,c_8906]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11562,plain,
% 3.53/1.00      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top
% 3.53/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_11536,c_4683]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_12095,plain,
% 3.53/1.00      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2240,c_11562]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_12534,plain,
% 3.53/1.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_12532,c_12095]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11304,plain,
% 3.53/1.00      ( v1_funct_2(sK3,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_11290,c_2219]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11552,plain,
% 3.53/1.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_11536,c_11304]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(contradiction,plain,
% 3.53/1.00      ( $false ),
% 3.53/1.00      inference(minisat,[status(thm)],[c_12534,c_11552]) ).
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  ------                               Statistics
% 3.53/1.00  
% 3.53/1.00  ------ General
% 3.53/1.00  
% 3.53/1.00  abstr_ref_over_cycles:                  0
% 3.53/1.00  abstr_ref_under_cycles:                 0
% 3.53/1.00  gc_basic_clause_elim:                   0
% 3.53/1.00  forced_gc_time:                         0
% 3.53/1.00  parsing_time:                           0.012
% 3.53/1.00  unif_index_cands_time:                  0.
% 3.53/1.00  unif_index_add_time:                    0.
% 3.53/1.00  orderings_time:                         0.
% 3.53/1.00  out_proof_time:                         0.022
% 3.53/1.00  total_time:                             0.435
% 3.53/1.00  num_of_symbols:                         50
% 3.53/1.00  num_of_terms:                           11545
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing
% 3.53/1.00  
% 3.53/1.00  num_of_splits:                          0
% 3.53/1.00  num_of_split_atoms:                     0
% 3.53/1.00  num_of_reused_defs:                     0
% 3.53/1.00  num_eq_ax_congr_red:                    15
% 3.53/1.00  num_of_sem_filtered_clauses:            1
% 3.53/1.00  num_of_subtypes:                        0
% 3.53/1.00  monotx_restored_types:                  0
% 3.53/1.00  sat_num_of_epr_types:                   0
% 3.53/1.00  sat_num_of_non_cyclic_types:            0
% 3.53/1.00  sat_guarded_non_collapsed_types:        0
% 3.53/1.00  num_pure_diseq_elim:                    0
% 3.53/1.00  simp_replaced_by:                       0
% 3.53/1.00  res_preprocessed:                       173
% 3.53/1.00  prep_upred:                             0
% 3.53/1.00  prep_unflattend:                        16
% 3.53/1.00  smt_new_axioms:                         0
% 3.53/1.00  pred_elim_cands:                        7
% 3.53/1.00  pred_elim:                              0
% 3.53/1.00  pred_elim_cl:                           0
% 3.53/1.00  pred_elim_cycles:                       2
% 3.53/1.00  merged_defs:                            16
% 3.53/1.00  merged_defs_ncl:                        0
% 3.53/1.00  bin_hyper_res:                          16
% 3.53/1.00  prep_cycles:                            4
% 3.53/1.00  pred_elim_time:                         0.019
% 3.53/1.00  splitting_time:                         0.
% 3.53/1.00  sem_filter_time:                        0.
% 3.53/1.00  monotx_time:                            0.001
% 3.53/1.00  subtype_inf_time:                       0.
% 3.53/1.00  
% 3.53/1.00  ------ Problem properties
% 3.53/1.00  
% 3.53/1.00  clauses:                                36
% 3.53/1.00  conjectures:                            13
% 3.53/1.00  epr:                                    9
% 3.53/1.00  horn:                                   30
% 3.53/1.00  ground:                                 13
% 3.53/1.00  unary:                                  15
% 3.53/1.00  binary:                                 8
% 3.53/1.00  lits:                                   105
% 3.53/1.00  lits_eq:                                17
% 3.53/1.00  fd_pure:                                0
% 3.53/1.00  fd_pseudo:                              0
% 3.53/1.00  fd_cond:                                4
% 3.53/1.00  fd_pseudo_cond:                         1
% 3.53/1.00  ac_symbols:                             0
% 3.53/1.00  
% 3.53/1.00  ------ Propositional Solver
% 3.53/1.00  
% 3.53/1.00  prop_solver_calls:                      32
% 3.53/1.00  prop_fast_solver_calls:                 1801
% 3.53/1.00  smt_solver_calls:                       0
% 3.53/1.00  smt_fast_solver_calls:                  0
% 3.53/1.00  prop_num_of_clauses:                    5357
% 3.53/1.00  prop_preprocess_simplified:             10369
% 3.53/1.00  prop_fo_subsumed:                       78
% 3.53/1.00  prop_solver_time:                       0.
% 3.53/1.00  smt_solver_time:                        0.
% 3.53/1.00  smt_fast_solver_time:                   0.
% 3.53/1.00  prop_fast_solver_time:                  0.
% 3.53/1.00  prop_unsat_core_time:                   0.
% 3.53/1.00  
% 3.53/1.00  ------ QBF
% 3.53/1.00  
% 3.53/1.00  qbf_q_res:                              0
% 3.53/1.00  qbf_num_tautologies:                    0
% 3.53/1.00  qbf_prep_cycles:                        0
% 3.53/1.00  
% 3.53/1.00  ------ BMC1
% 3.53/1.00  
% 3.53/1.00  bmc1_current_bound:                     -1
% 3.53/1.00  bmc1_last_solved_bound:                 -1
% 3.53/1.00  bmc1_unsat_core_size:                   -1
% 3.53/1.00  bmc1_unsat_core_parents_size:           -1
% 3.53/1.00  bmc1_merge_next_fun:                    0
% 3.53/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.53/1.00  
% 3.53/1.00  ------ Instantiation
% 3.53/1.00  
% 3.53/1.00  inst_num_of_clauses:                    1384
% 3.53/1.00  inst_num_in_passive:                    215
% 3.53/1.00  inst_num_in_active:                     757
% 3.53/1.00  inst_num_in_unprocessed:                412
% 3.53/1.00  inst_num_of_loops:                      910
% 3.53/1.00  inst_num_of_learning_restarts:          0
% 3.53/1.00  inst_num_moves_active_passive:          149
% 3.53/1.00  inst_lit_activity:                      0
% 3.53/1.00  inst_lit_activity_moves:                0
% 3.53/1.00  inst_num_tautologies:                   0
% 3.53/1.00  inst_num_prop_implied:                  0
% 3.53/1.00  inst_num_existing_simplified:           0
% 3.53/1.00  inst_num_eq_res_simplified:             0
% 3.53/1.00  inst_num_child_elim:                    0
% 3.53/1.00  inst_num_of_dismatching_blockings:      315
% 3.53/1.00  inst_num_of_non_proper_insts:           1913
% 3.53/1.00  inst_num_of_duplicates:                 0
% 3.53/1.00  inst_inst_num_from_inst_to_res:         0
% 3.53/1.00  inst_dismatching_checking_time:         0.
% 3.53/1.00  
% 3.53/1.00  ------ Resolution
% 3.53/1.00  
% 3.53/1.00  res_num_of_clauses:                     0
% 3.53/1.00  res_num_in_passive:                     0
% 3.53/1.00  res_num_in_active:                      0
% 3.53/1.00  res_num_of_loops:                       177
% 3.53/1.00  res_forward_subset_subsumed:            135
% 3.53/1.00  res_backward_subset_subsumed:           0
% 3.53/1.00  res_forward_subsumed:                   0
% 3.53/1.00  res_backward_subsumed:                  0
% 3.53/1.00  res_forward_subsumption_resolution:     0
% 3.53/1.00  res_backward_subsumption_resolution:    0
% 3.53/1.00  res_clause_to_clause_subsumption:       1679
% 3.53/1.00  res_orphan_elimination:                 0
% 3.53/1.00  res_tautology_del:                      157
% 3.53/1.00  res_num_eq_res_simplified:              0
% 3.53/1.00  res_num_sel_changes:                    0
% 3.53/1.00  res_moves_from_active_to_pass:          0
% 3.53/1.00  
% 3.53/1.00  ------ Superposition
% 3.53/1.00  
% 3.53/1.00  sup_time_total:                         0.
% 3.53/1.00  sup_time_generating:                    0.
% 3.53/1.00  sup_time_sim_full:                      0.
% 3.53/1.00  sup_time_sim_immed:                     0.
% 3.53/1.00  
% 3.53/1.00  sup_num_of_clauses:                     356
% 3.53/1.00  sup_num_in_active:                      82
% 3.53/1.00  sup_num_in_passive:                     274
% 3.53/1.00  sup_num_of_loops:                       181
% 3.53/1.00  sup_fw_superposition:                   266
% 3.53/1.00  sup_bw_superposition:                   403
% 3.53/1.00  sup_immediate_simplified:               272
% 3.53/1.00  sup_given_eliminated:                   2
% 3.53/1.00  comparisons_done:                       0
% 3.53/1.00  comparisons_avoided:                    18
% 3.53/1.00  
% 3.53/1.00  ------ Simplifications
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  sim_fw_subset_subsumed:                 64
% 3.53/1.00  sim_bw_subset_subsumed:                 106
% 3.53/1.00  sim_fw_subsumed:                        25
% 3.53/1.00  sim_bw_subsumed:                        8
% 3.53/1.00  sim_fw_subsumption_res:                 0
% 3.53/1.00  sim_bw_subsumption_res:                 0
% 3.53/1.00  sim_tautology_del:                      6
% 3.53/1.00  sim_eq_tautology_del:                   27
% 3.53/1.00  sim_eq_res_simp:                        0
% 3.53/1.00  sim_fw_demodulated:                     139
% 3.53/1.00  sim_bw_demodulated:                     95
% 3.53/1.00  sim_light_normalised:                   122
% 3.53/1.00  sim_joinable_taut:                      0
% 3.53/1.00  sim_joinable_simp:                      0
% 3.53/1.00  sim_ac_normalised:                      0
% 3.53/1.00  sim_smt_subsumption:                    0
% 3.53/1.00  
%------------------------------------------------------------------------------
