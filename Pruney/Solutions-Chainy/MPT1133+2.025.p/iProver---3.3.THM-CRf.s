%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:53 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  269 (20665 expanded)
%              Number of clauses        :  190 (4806 expanded)
%              Number of leaves         :   21 (6201 expanded)
%              Depth                    :   28
%              Number of atoms          : 1206 (241078 expanded)
%              Number of equality atoms :  486 (27806 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

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
    inference(ennf_transformation,[],[f23])).

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

fof(f61,plain,(
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

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f66,plain,(
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
     => ( ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK4 = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
              | ~ v5_pre_topc(sK3,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK3,X0,X1) )
            & sK3 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
                  | ~ v5_pre_topc(X2,X0,sK2) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
                  | v5_pre_topc(X2,X0,sK2) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK1,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK1,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ v5_pre_topc(sK3,sK1,sK2) )
    & ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | v5_pre_topc(sK3,sK1,sK2) )
    & sK3 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f62,f66,f65,f64,f63])).

fof(f108,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(cnf_transformation,[],[f67])).

fof(f13,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f107,plain,(
    v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f67])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f21])).

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

fof(f60,plain,(
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

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f119,plain,(
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
    inference(equality_resolution,[],[f98])).

fof(f99,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f100,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f101,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f102,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f106,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f105,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f67])).

fof(f109,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f67])).

fof(f110,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f104,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f67])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f94,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f92,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

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

fof(f59,plain,(
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

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f59])).

fof(f118,plain,(
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
    inference(equality_resolution,[],[f95])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f120,plain,(
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
    inference(equality_resolution,[],[f97])).

fof(f111,plain,
    ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f96,plain,(
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
    inference(cnf_transformation,[],[f59])).

fof(f117,plain,(
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
    inference(equality_resolution,[],[f96])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f116,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f115,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1794,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1808,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6680,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK4) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1808])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1814,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3799,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1794,c_1814])).

cnf(c_6692,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6680,c_3799])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_6733,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6692])).

cnf(c_8976,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6692,c_35,c_6733])).

cnf(c_8977,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_8976])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1816,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4952,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1816])).

cnf(c_9007,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8977,c_4952])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_138,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11613,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9007,c_138])).

cnf(c_11614,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
    | v1_xboole_0(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_11613])).

cnf(c_1822,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1821,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3595,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1822,c_1821])).

cnf(c_11620,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11614,c_3595])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f119])).

cnf(c_1798,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4704,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1798])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_44,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_45,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_46,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_47,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_51,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_52,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1791,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_33,negated_conjecture,
    ( sK3 = sK4 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1843,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1791,c_33])).

cnf(c_32,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1795,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1908,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1795,c_33])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1790,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1840,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1790,c_33])).

cnf(c_25,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2158,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2159,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2158])).

cnf(c_26,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2176,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2177,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2176])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2377,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2378,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2377])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f118])).

cnf(c_2344,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
    | ~ v5_pre_topc(X0,sK1,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2820,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v5_pre_topc(X0,sK1,sK2)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_3518,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v5_pre_topc(sK4,sK1,sK2)
    | ~ v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2820])).

cnf(c_3519,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3518])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f120])).

cnf(c_1797,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3330,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1797])).

cnf(c_31,negated_conjecture,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1796,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1913,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1796,c_33])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f117])).

cnf(c_2334,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
    | v5_pre_topc(X0,sK1,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2774,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | v5_pre_topc(X0,sK1,sK2)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_2334])).

cnf(c_3454,plain,
    ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | v5_pre_topc(sK4,sK1,sK2)
    | ~ v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2774])).

cnf(c_3455,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3454])).

cnf(c_3941,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3330,c_44,c_45,c_46,c_47,c_51,c_52,c_1843,c_1913,c_1840,c_2159,c_2177,c_2378,c_3455])).

cnf(c_3942,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3941])).

cnf(c_5046,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4704,c_44,c_45,c_46,c_47,c_51,c_52,c_1843,c_1908,c_1840,c_2159,c_2177,c_2378,c_3519,c_3942])).

cnf(c_5047,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5046])).

cnf(c_26054,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11620,c_5047])).

cnf(c_1793,plain,
    ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_26060,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11620,c_1793])).

cnf(c_6681,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4) = u1_struct_0(sK1)
    | u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_1808])).

cnf(c_3800,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1843,c_1814])).

cnf(c_6685,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6681,c_3800])).

cnf(c_7187,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6685,c_1840])).

cnf(c_7188,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) = k1_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_7187])).

cnf(c_4953,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_1816])).

cnf(c_7212,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7188,c_4953])).

cnf(c_8502,plain,
    ( v1_xboole_0(sK4) = iProver_top
    | u1_struct_0(sK1) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7212,c_138])).

cnf(c_8503,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | v1_xboole_0(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_8502])).

cnf(c_8508,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8503,c_3595])).

cnf(c_26059,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11620,c_1794])).

cnf(c_1800,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6255,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1800])).

cnf(c_2155,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2156,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2155])).

cnf(c_2173,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2174,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2173])).

cnf(c_2369,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2370,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2369])).

cnf(c_2364,plain,
    ( ~ v5_pre_topc(X0,sK1,X1)
    | v5_pre_topc(X0,sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2900,plain,
    ( v5_pre_topc(X0,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v5_pre_topc(X0,sK1,sK2)
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_2364])).

cnf(c_3677,plain,
    ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v5_pre_topc(sK4,sK1,sK2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2900])).

cnf(c_3678,plain,
    ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3677])).

cnf(c_1799,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5112,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1799])).

cnf(c_2354,plain,
    ( v5_pre_topc(X0,sK1,X1)
    | ~ v5_pre_topc(X0,sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2860,plain,
    ( ~ v5_pre_topc(X0,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(X0,sK1,sK2)
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_2354])).

cnf(c_3613,plain,
    ( ~ v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK4,sK1,sK2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2860])).

cnf(c_3614,plain,
    ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v5_pre_topc(sK4,sK1,sK2) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3613])).

cnf(c_5798,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5112,c_44,c_45,c_46,c_47,c_51,c_52,c_1843,c_1913,c_1840,c_2156,c_2174,c_2370,c_3614])).

cnf(c_5799,plain,
    ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5798])).

cnf(c_6742,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6255,c_44,c_45,c_46,c_47,c_51,c_52,c_1843,c_1908,c_1840,c_2156,c_2174,c_2370,c_3678,c_5799])).

cnf(c_6743,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6742])).

cnf(c_20640,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8508,c_6743])).

cnf(c_27267,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26059,c_20640])).

cnf(c_27301,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK4,k1_relat_1(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8508,c_27267])).

cnf(c_27491,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26054,c_26060,c_27301])).

cnf(c_27607,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_27491,c_3799])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1818,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1809,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5260,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1818,c_1809])).

cnf(c_3798,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1818,c_1814])).

cnf(c_5270,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5260,c_3798])).

cnf(c_14,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_100,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_102,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_2214,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2217,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2214])).

cnf(c_2219,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_3923,plain,
    ( ~ v1_xboole_0(k1_relset_1(k1_xboole_0,X0,X1))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3924,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_xboole_0(k1_relset_1(k1_xboole_0,X0,X1)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3923])).

cnf(c_3926,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3924])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1815,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1817,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4808,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k1_relset_1(X1,X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1815,c_1817])).

cnf(c_4894,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4808])).

cnf(c_5286,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5270])).

cnf(c_6041,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5270,c_102,c_138,c_2219,c_3926,c_4894,c_5286])).

cnf(c_27643,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_27607,c_6041])).

cnf(c_27614,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_27491,c_1793])).

cnf(c_6677,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1818,c_1808])).

cnf(c_28263,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27614,c_6677])).

cnf(c_136,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_901,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_13965,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | X3 != X0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != X2
    | u1_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_13966,plain,
    ( X0 != X1
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != X2
    | u1_struct_0(sK1) != X3
    | v1_funct_2(X1,X3,X2) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13965])).

cnf(c_13968,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != k1_xboole_0
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13966])).

cnf(c_9009,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8977,c_1794])).

cnf(c_7208,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7188,c_5047])).

cnf(c_11299,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
    | u1_struct_0(sK1) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9009,c_7208])).

cnf(c_7220,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7188,c_1843])).

cnf(c_7221,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7188,c_1840])).

cnf(c_9003,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8977,c_6743])).

cnf(c_11329,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8977,c_9003])).

cnf(c_12292,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11299,c_7220,c_7221,c_11329])).

cnf(c_12293,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
    | u1_struct_0(sK1) = k1_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_12292])).

cnf(c_12335,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12293,c_7208])).

cnf(c_18618,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7188,c_12335])).

cnf(c_19549,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK4)
    | v1_funct_2(sK4,k1_relat_1(sK4),k1_xboole_0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12293,c_18618])).

cnf(c_27521,plain,
    ( u1_struct_0(sK1) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27491,c_19549])).

cnf(c_27981,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27521,c_6041])).

cnf(c_27592,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27491,c_6743])).

cnf(c_28479,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27592,c_1818])).

cnf(c_29423,plain,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28263,c_102,c_136,c_0,c_138,c_2219,c_3926,c_4894,c_13968,c_27981,c_28479])).

cnf(c_30109,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27643,c_29423])).

cnf(c_27601,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27491,c_5047])).

cnf(c_28484,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27601,c_1818])).

cnf(c_30118,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30109,c_28484])).

cnf(c_895,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2508,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_13335,plain,
    ( X0 = sK3
    | X0 != sK4
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_2508])).

cnf(c_13336,plain,
    ( sK3 != sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_13335])).

cnf(c_9769,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_9770,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9769])).

cnf(c_894,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5756,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_2313,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | X2 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK1)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_5755,plain,
    ( v1_funct_2(X0,X1,u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | X1 != u1_struct_0(sK1)
    | X0 != sK3
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2313])).

cnf(c_5757,plain,
    ( X0 != u1_struct_0(sK1)
    | X1 != sK3
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v1_funct_2(X1,X0,u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5755])).

cnf(c_5759,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != sK3
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5757])).

cnf(c_2489,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_2490,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2489])).

cnf(c_49,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30118,c_27981,c_27491,c_13336,c_9770,c_5756,c_5759,c_4894,c_3926,c_2490,c_2219,c_138,c_0,c_136,c_102,c_33,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:19 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 7.94/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/1.51  
% 7.94/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.94/1.51  
% 7.94/1.51  ------  iProver source info
% 7.94/1.51  
% 7.94/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.94/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.94/1.51  git: non_committed_changes: false
% 7.94/1.51  git: last_make_outside_of_git: false
% 7.94/1.51  
% 7.94/1.51  ------ 
% 7.94/1.51  
% 7.94/1.51  ------ Input Options
% 7.94/1.51  
% 7.94/1.51  --out_options                           all
% 7.94/1.51  --tptp_safe_out                         true
% 7.94/1.51  --problem_path                          ""
% 7.94/1.51  --include_path                          ""
% 7.94/1.51  --clausifier                            res/vclausify_rel
% 7.94/1.51  --clausifier_options                    --mode clausify
% 7.94/1.51  --stdin                                 false
% 7.94/1.51  --stats_out                             all
% 7.94/1.51  
% 7.94/1.51  ------ General Options
% 7.94/1.51  
% 7.94/1.51  --fof                                   false
% 7.94/1.51  --time_out_real                         305.
% 7.94/1.51  --time_out_virtual                      -1.
% 7.94/1.51  --symbol_type_check                     false
% 7.94/1.51  --clausify_out                          false
% 7.94/1.51  --sig_cnt_out                           false
% 7.94/1.51  --trig_cnt_out                          false
% 7.94/1.51  --trig_cnt_out_tolerance                1.
% 7.94/1.51  --trig_cnt_out_sk_spl                   false
% 7.94/1.51  --abstr_cl_out                          false
% 7.94/1.51  
% 7.94/1.51  ------ Global Options
% 7.94/1.51  
% 7.94/1.51  --schedule                              default
% 7.94/1.51  --add_important_lit                     false
% 7.94/1.51  --prop_solver_per_cl                    1000
% 7.94/1.51  --min_unsat_core                        false
% 7.94/1.51  --soft_assumptions                      false
% 7.94/1.51  --soft_lemma_size                       3
% 7.94/1.51  --prop_impl_unit_size                   0
% 7.94/1.51  --prop_impl_unit                        []
% 7.94/1.51  --share_sel_clauses                     true
% 7.94/1.51  --reset_solvers                         false
% 7.94/1.51  --bc_imp_inh                            [conj_cone]
% 7.94/1.51  --conj_cone_tolerance                   3.
% 7.94/1.51  --extra_neg_conj                        none
% 7.94/1.51  --large_theory_mode                     true
% 7.94/1.51  --prolific_symb_bound                   200
% 7.94/1.51  --lt_threshold                          2000
% 7.94/1.51  --clause_weak_htbl                      true
% 7.94/1.51  --gc_record_bc_elim                     false
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing Options
% 7.94/1.51  
% 7.94/1.51  --preprocessing_flag                    true
% 7.94/1.51  --time_out_prep_mult                    0.1
% 7.94/1.51  --splitting_mode                        input
% 7.94/1.51  --splitting_grd                         true
% 7.94/1.51  --splitting_cvd                         false
% 7.94/1.51  --splitting_cvd_svl                     false
% 7.94/1.51  --splitting_nvd                         32
% 7.94/1.51  --sub_typing                            true
% 7.94/1.51  --prep_gs_sim                           true
% 7.94/1.51  --prep_unflatten                        true
% 7.94/1.51  --prep_res_sim                          true
% 7.94/1.51  --prep_upred                            true
% 7.94/1.51  --prep_sem_filter                       exhaustive
% 7.94/1.51  --prep_sem_filter_out                   false
% 7.94/1.51  --pred_elim                             true
% 7.94/1.51  --res_sim_input                         true
% 7.94/1.51  --eq_ax_congr_red                       true
% 7.94/1.51  --pure_diseq_elim                       true
% 7.94/1.51  --brand_transform                       false
% 7.94/1.51  --non_eq_to_eq                          false
% 7.94/1.51  --prep_def_merge                        true
% 7.94/1.51  --prep_def_merge_prop_impl              false
% 7.94/1.51  --prep_def_merge_mbd                    true
% 7.94/1.51  --prep_def_merge_tr_red                 false
% 7.94/1.51  --prep_def_merge_tr_cl                  false
% 7.94/1.51  --smt_preprocessing                     true
% 7.94/1.51  --smt_ac_axioms                         fast
% 7.94/1.51  --preprocessed_out                      false
% 7.94/1.51  --preprocessed_stats                    false
% 7.94/1.51  
% 7.94/1.51  ------ Abstraction refinement Options
% 7.94/1.51  
% 7.94/1.51  --abstr_ref                             []
% 7.94/1.51  --abstr_ref_prep                        false
% 7.94/1.51  --abstr_ref_until_sat                   false
% 7.94/1.51  --abstr_ref_sig_restrict                funpre
% 7.94/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.94/1.51  --abstr_ref_under                       []
% 7.94/1.51  
% 7.94/1.51  ------ SAT Options
% 7.94/1.51  
% 7.94/1.51  --sat_mode                              false
% 7.94/1.51  --sat_fm_restart_options                ""
% 7.94/1.51  --sat_gr_def                            false
% 7.94/1.51  --sat_epr_types                         true
% 7.94/1.51  --sat_non_cyclic_types                  false
% 7.94/1.51  --sat_finite_models                     false
% 7.94/1.51  --sat_fm_lemmas                         false
% 7.94/1.51  --sat_fm_prep                           false
% 7.94/1.51  --sat_fm_uc_incr                        true
% 7.94/1.51  --sat_out_model                         small
% 7.94/1.51  --sat_out_clauses                       false
% 7.94/1.51  
% 7.94/1.51  ------ QBF Options
% 7.94/1.51  
% 7.94/1.51  --qbf_mode                              false
% 7.94/1.51  --qbf_elim_univ                         false
% 7.94/1.51  --qbf_dom_inst                          none
% 7.94/1.51  --qbf_dom_pre_inst                      false
% 7.94/1.51  --qbf_sk_in                             false
% 7.94/1.51  --qbf_pred_elim                         true
% 7.94/1.51  --qbf_split                             512
% 7.94/1.51  
% 7.94/1.51  ------ BMC1 Options
% 7.94/1.51  
% 7.94/1.51  --bmc1_incremental                      false
% 7.94/1.51  --bmc1_axioms                           reachable_all
% 7.94/1.51  --bmc1_min_bound                        0
% 7.94/1.51  --bmc1_max_bound                        -1
% 7.94/1.51  --bmc1_max_bound_default                -1
% 7.94/1.51  --bmc1_symbol_reachability              true
% 7.94/1.51  --bmc1_property_lemmas                  false
% 7.94/1.51  --bmc1_k_induction                      false
% 7.94/1.51  --bmc1_non_equiv_states                 false
% 7.94/1.51  --bmc1_deadlock                         false
% 7.94/1.51  --bmc1_ucm                              false
% 7.94/1.51  --bmc1_add_unsat_core                   none
% 7.94/1.51  --bmc1_unsat_core_children              false
% 7.94/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.94/1.51  --bmc1_out_stat                         full
% 7.94/1.51  --bmc1_ground_init                      false
% 7.94/1.51  --bmc1_pre_inst_next_state              false
% 7.94/1.51  --bmc1_pre_inst_state                   false
% 7.94/1.51  --bmc1_pre_inst_reach_state             false
% 7.94/1.51  --bmc1_out_unsat_core                   false
% 7.94/1.51  --bmc1_aig_witness_out                  false
% 7.94/1.51  --bmc1_verbose                          false
% 7.94/1.51  --bmc1_dump_clauses_tptp                false
% 7.94/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.94/1.51  --bmc1_dump_file                        -
% 7.94/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.94/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.94/1.51  --bmc1_ucm_extend_mode                  1
% 7.94/1.51  --bmc1_ucm_init_mode                    2
% 7.94/1.51  --bmc1_ucm_cone_mode                    none
% 7.94/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.94/1.51  --bmc1_ucm_relax_model                  4
% 7.94/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.94/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.94/1.51  --bmc1_ucm_layered_model                none
% 7.94/1.51  --bmc1_ucm_max_lemma_size               10
% 7.94/1.51  
% 7.94/1.51  ------ AIG Options
% 7.94/1.51  
% 7.94/1.51  --aig_mode                              false
% 7.94/1.51  
% 7.94/1.51  ------ Instantiation Options
% 7.94/1.51  
% 7.94/1.51  --instantiation_flag                    true
% 7.94/1.51  --inst_sos_flag                         false
% 7.94/1.51  --inst_sos_phase                        true
% 7.94/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.94/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.94/1.51  --inst_lit_sel_side                     num_symb
% 7.94/1.51  --inst_solver_per_active                1400
% 7.94/1.51  --inst_solver_calls_frac                1.
% 7.94/1.51  --inst_passive_queue_type               priority_queues
% 7.94/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.94/1.51  --inst_passive_queues_freq              [25;2]
% 7.94/1.51  --inst_dismatching                      true
% 7.94/1.51  --inst_eager_unprocessed_to_passive     true
% 7.94/1.51  --inst_prop_sim_given                   true
% 7.94/1.51  --inst_prop_sim_new                     false
% 7.94/1.51  --inst_subs_new                         false
% 7.94/1.51  --inst_eq_res_simp                      false
% 7.94/1.51  --inst_subs_given                       false
% 7.94/1.51  --inst_orphan_elimination               true
% 7.94/1.51  --inst_learning_loop_flag               true
% 7.94/1.51  --inst_learning_start                   3000
% 7.94/1.51  --inst_learning_factor                  2
% 7.94/1.51  --inst_start_prop_sim_after_learn       3
% 7.94/1.51  --inst_sel_renew                        solver
% 7.94/1.51  --inst_lit_activity_flag                true
% 7.94/1.51  --inst_restr_to_given                   false
% 7.94/1.51  --inst_activity_threshold               500
% 7.94/1.51  --inst_out_proof                        true
% 7.94/1.51  
% 7.94/1.51  ------ Resolution Options
% 7.94/1.51  
% 7.94/1.51  --resolution_flag                       true
% 7.94/1.51  --res_lit_sel                           adaptive
% 7.94/1.51  --res_lit_sel_side                      none
% 7.94/1.51  --res_ordering                          kbo
% 7.94/1.51  --res_to_prop_solver                    active
% 7.94/1.51  --res_prop_simpl_new                    false
% 7.94/1.51  --res_prop_simpl_given                  true
% 7.94/1.51  --res_passive_queue_type                priority_queues
% 7.94/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.94/1.51  --res_passive_queues_freq               [15;5]
% 7.94/1.51  --res_forward_subs                      full
% 7.94/1.51  --res_backward_subs                     full
% 7.94/1.51  --res_forward_subs_resolution           true
% 7.94/1.51  --res_backward_subs_resolution          true
% 7.94/1.51  --res_orphan_elimination                true
% 7.94/1.51  --res_time_limit                        2.
% 7.94/1.51  --res_out_proof                         true
% 7.94/1.51  
% 7.94/1.51  ------ Superposition Options
% 7.94/1.51  
% 7.94/1.51  --superposition_flag                    true
% 7.94/1.51  --sup_passive_queue_type                priority_queues
% 7.94/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.94/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.94/1.51  --demod_completeness_check              fast
% 7.94/1.51  --demod_use_ground                      true
% 7.94/1.51  --sup_to_prop_solver                    passive
% 7.94/1.51  --sup_prop_simpl_new                    true
% 7.94/1.51  --sup_prop_simpl_given                  true
% 7.94/1.51  --sup_fun_splitting                     false
% 7.94/1.51  --sup_smt_interval                      50000
% 7.94/1.51  
% 7.94/1.51  ------ Superposition Simplification Setup
% 7.94/1.51  
% 7.94/1.51  --sup_indices_passive                   []
% 7.94/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.94/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_full_bw                           [BwDemod]
% 7.94/1.51  --sup_immed_triv                        [TrivRules]
% 7.94/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_immed_bw_main                     []
% 7.94/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.94/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.51  
% 7.94/1.51  ------ Combination Options
% 7.94/1.51  
% 7.94/1.51  --comb_res_mult                         3
% 7.94/1.51  --comb_sup_mult                         2
% 7.94/1.51  --comb_inst_mult                        10
% 7.94/1.51  
% 7.94/1.51  ------ Debug Options
% 7.94/1.51  
% 7.94/1.51  --dbg_backtrace                         false
% 7.94/1.51  --dbg_dump_prop_clauses                 false
% 7.94/1.51  --dbg_dump_prop_clauses_file            -
% 7.94/1.51  --dbg_out_stat                          false
% 7.94/1.51  ------ Parsing...
% 7.94/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.51  ------ Proving...
% 7.94/1.51  ------ Problem Properties 
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  clauses                                 40
% 7.94/1.51  conjectures                             13
% 7.94/1.51  EPR                                     9
% 7.94/1.51  Horn                                    34
% 7.94/1.51  unary                                   13
% 7.94/1.51  binary                                  9
% 7.94/1.51  lits                                    121
% 7.94/1.51  lits eq                                 15
% 7.94/1.51  fd_pure                                 0
% 7.94/1.51  fd_pseudo                               0
% 7.94/1.51  fd_cond                                 3
% 7.94/1.51  fd_pseudo_cond                          1
% 7.94/1.51  AC symbols                              0
% 7.94/1.51  
% 7.94/1.51  ------ Schedule dynamic 5 is on 
% 7.94/1.51  
% 7.94/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  ------ 
% 7.94/1.51  Current options:
% 7.94/1.51  ------ 
% 7.94/1.51  
% 7.94/1.51  ------ Input Options
% 7.94/1.51  
% 7.94/1.51  --out_options                           all
% 7.94/1.51  --tptp_safe_out                         true
% 7.94/1.51  --problem_path                          ""
% 7.94/1.51  --include_path                          ""
% 7.94/1.51  --clausifier                            res/vclausify_rel
% 7.94/1.51  --clausifier_options                    --mode clausify
% 7.94/1.51  --stdin                                 false
% 7.94/1.51  --stats_out                             all
% 7.94/1.51  
% 7.94/1.51  ------ General Options
% 7.94/1.51  
% 7.94/1.51  --fof                                   false
% 7.94/1.51  --time_out_real                         305.
% 7.94/1.51  --time_out_virtual                      -1.
% 7.94/1.51  --symbol_type_check                     false
% 7.94/1.51  --clausify_out                          false
% 7.94/1.51  --sig_cnt_out                           false
% 7.94/1.51  --trig_cnt_out                          false
% 7.94/1.51  --trig_cnt_out_tolerance                1.
% 7.94/1.51  --trig_cnt_out_sk_spl                   false
% 7.94/1.51  --abstr_cl_out                          false
% 7.94/1.51  
% 7.94/1.51  ------ Global Options
% 7.94/1.51  
% 7.94/1.51  --schedule                              default
% 7.94/1.51  --add_important_lit                     false
% 7.94/1.51  --prop_solver_per_cl                    1000
% 7.94/1.51  --min_unsat_core                        false
% 7.94/1.51  --soft_assumptions                      false
% 7.94/1.51  --soft_lemma_size                       3
% 7.94/1.51  --prop_impl_unit_size                   0
% 7.94/1.51  --prop_impl_unit                        []
% 7.94/1.51  --share_sel_clauses                     true
% 7.94/1.51  --reset_solvers                         false
% 7.94/1.51  --bc_imp_inh                            [conj_cone]
% 7.94/1.51  --conj_cone_tolerance                   3.
% 7.94/1.51  --extra_neg_conj                        none
% 7.94/1.51  --large_theory_mode                     true
% 7.94/1.51  --prolific_symb_bound                   200
% 7.94/1.51  --lt_threshold                          2000
% 7.94/1.51  --clause_weak_htbl                      true
% 7.94/1.51  --gc_record_bc_elim                     false
% 7.94/1.51  
% 7.94/1.51  ------ Preprocessing Options
% 7.94/1.51  
% 7.94/1.51  --preprocessing_flag                    true
% 7.94/1.51  --time_out_prep_mult                    0.1
% 7.94/1.51  --splitting_mode                        input
% 7.94/1.51  --splitting_grd                         true
% 7.94/1.51  --splitting_cvd                         false
% 7.94/1.51  --splitting_cvd_svl                     false
% 7.94/1.51  --splitting_nvd                         32
% 7.94/1.51  --sub_typing                            true
% 7.94/1.51  --prep_gs_sim                           true
% 7.94/1.51  --prep_unflatten                        true
% 7.94/1.51  --prep_res_sim                          true
% 7.94/1.51  --prep_upred                            true
% 7.94/1.51  --prep_sem_filter                       exhaustive
% 7.94/1.51  --prep_sem_filter_out                   false
% 7.94/1.51  --pred_elim                             true
% 7.94/1.51  --res_sim_input                         true
% 7.94/1.51  --eq_ax_congr_red                       true
% 7.94/1.51  --pure_diseq_elim                       true
% 7.94/1.51  --brand_transform                       false
% 7.94/1.51  --non_eq_to_eq                          false
% 7.94/1.51  --prep_def_merge                        true
% 7.94/1.51  --prep_def_merge_prop_impl              false
% 7.94/1.51  --prep_def_merge_mbd                    true
% 7.94/1.51  --prep_def_merge_tr_red                 false
% 7.94/1.51  --prep_def_merge_tr_cl                  false
% 7.94/1.51  --smt_preprocessing                     true
% 7.94/1.51  --smt_ac_axioms                         fast
% 7.94/1.51  --preprocessed_out                      false
% 7.94/1.51  --preprocessed_stats                    false
% 7.94/1.51  
% 7.94/1.51  ------ Abstraction refinement Options
% 7.94/1.51  
% 7.94/1.51  --abstr_ref                             []
% 7.94/1.51  --abstr_ref_prep                        false
% 7.94/1.51  --abstr_ref_until_sat                   false
% 7.94/1.51  --abstr_ref_sig_restrict                funpre
% 7.94/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.94/1.51  --abstr_ref_under                       []
% 7.94/1.51  
% 7.94/1.51  ------ SAT Options
% 7.94/1.51  
% 7.94/1.51  --sat_mode                              false
% 7.94/1.51  --sat_fm_restart_options                ""
% 7.94/1.51  --sat_gr_def                            false
% 7.94/1.51  --sat_epr_types                         true
% 7.94/1.51  --sat_non_cyclic_types                  false
% 7.94/1.51  --sat_finite_models                     false
% 7.94/1.51  --sat_fm_lemmas                         false
% 7.94/1.51  --sat_fm_prep                           false
% 7.94/1.51  --sat_fm_uc_incr                        true
% 7.94/1.51  --sat_out_model                         small
% 7.94/1.51  --sat_out_clauses                       false
% 7.94/1.51  
% 7.94/1.51  ------ QBF Options
% 7.94/1.51  
% 7.94/1.51  --qbf_mode                              false
% 7.94/1.51  --qbf_elim_univ                         false
% 7.94/1.51  --qbf_dom_inst                          none
% 7.94/1.51  --qbf_dom_pre_inst                      false
% 7.94/1.51  --qbf_sk_in                             false
% 7.94/1.51  --qbf_pred_elim                         true
% 7.94/1.51  --qbf_split                             512
% 7.94/1.51  
% 7.94/1.51  ------ BMC1 Options
% 7.94/1.51  
% 7.94/1.51  --bmc1_incremental                      false
% 7.94/1.51  --bmc1_axioms                           reachable_all
% 7.94/1.51  --bmc1_min_bound                        0
% 7.94/1.51  --bmc1_max_bound                        -1
% 7.94/1.51  --bmc1_max_bound_default                -1
% 7.94/1.51  --bmc1_symbol_reachability              true
% 7.94/1.51  --bmc1_property_lemmas                  false
% 7.94/1.51  --bmc1_k_induction                      false
% 7.94/1.51  --bmc1_non_equiv_states                 false
% 7.94/1.51  --bmc1_deadlock                         false
% 7.94/1.51  --bmc1_ucm                              false
% 7.94/1.51  --bmc1_add_unsat_core                   none
% 7.94/1.51  --bmc1_unsat_core_children              false
% 7.94/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.94/1.51  --bmc1_out_stat                         full
% 7.94/1.51  --bmc1_ground_init                      false
% 7.94/1.51  --bmc1_pre_inst_next_state              false
% 7.94/1.51  --bmc1_pre_inst_state                   false
% 7.94/1.51  --bmc1_pre_inst_reach_state             false
% 7.94/1.51  --bmc1_out_unsat_core                   false
% 7.94/1.51  --bmc1_aig_witness_out                  false
% 7.94/1.51  --bmc1_verbose                          false
% 7.94/1.51  --bmc1_dump_clauses_tptp                false
% 7.94/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.94/1.51  --bmc1_dump_file                        -
% 7.94/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.94/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.94/1.51  --bmc1_ucm_extend_mode                  1
% 7.94/1.51  --bmc1_ucm_init_mode                    2
% 7.94/1.51  --bmc1_ucm_cone_mode                    none
% 7.94/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.94/1.51  --bmc1_ucm_relax_model                  4
% 7.94/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.94/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.94/1.51  --bmc1_ucm_layered_model                none
% 7.94/1.51  --bmc1_ucm_max_lemma_size               10
% 7.94/1.51  
% 7.94/1.51  ------ AIG Options
% 7.94/1.51  
% 7.94/1.51  --aig_mode                              false
% 7.94/1.51  
% 7.94/1.51  ------ Instantiation Options
% 7.94/1.51  
% 7.94/1.51  --instantiation_flag                    true
% 7.94/1.51  --inst_sos_flag                         false
% 7.94/1.51  --inst_sos_phase                        true
% 7.94/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.94/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.94/1.51  --inst_lit_sel_side                     none
% 7.94/1.51  --inst_solver_per_active                1400
% 7.94/1.51  --inst_solver_calls_frac                1.
% 7.94/1.51  --inst_passive_queue_type               priority_queues
% 7.94/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.94/1.51  --inst_passive_queues_freq              [25;2]
% 7.94/1.51  --inst_dismatching                      true
% 7.94/1.51  --inst_eager_unprocessed_to_passive     true
% 7.94/1.51  --inst_prop_sim_given                   true
% 7.94/1.51  --inst_prop_sim_new                     false
% 7.94/1.51  --inst_subs_new                         false
% 7.94/1.51  --inst_eq_res_simp                      false
% 7.94/1.51  --inst_subs_given                       false
% 7.94/1.51  --inst_orphan_elimination               true
% 7.94/1.51  --inst_learning_loop_flag               true
% 7.94/1.51  --inst_learning_start                   3000
% 7.94/1.51  --inst_learning_factor                  2
% 7.94/1.51  --inst_start_prop_sim_after_learn       3
% 7.94/1.51  --inst_sel_renew                        solver
% 7.94/1.51  --inst_lit_activity_flag                true
% 7.94/1.51  --inst_restr_to_given                   false
% 7.94/1.51  --inst_activity_threshold               500
% 7.94/1.51  --inst_out_proof                        true
% 7.94/1.51  
% 7.94/1.51  ------ Resolution Options
% 7.94/1.51  
% 7.94/1.51  --resolution_flag                       false
% 7.94/1.51  --res_lit_sel                           adaptive
% 7.94/1.51  --res_lit_sel_side                      none
% 7.94/1.51  --res_ordering                          kbo
% 7.94/1.51  --res_to_prop_solver                    active
% 7.94/1.51  --res_prop_simpl_new                    false
% 7.94/1.51  --res_prop_simpl_given                  true
% 7.94/1.51  --res_passive_queue_type                priority_queues
% 7.94/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.94/1.51  --res_passive_queues_freq               [15;5]
% 7.94/1.51  --res_forward_subs                      full
% 7.94/1.51  --res_backward_subs                     full
% 7.94/1.51  --res_forward_subs_resolution           true
% 7.94/1.51  --res_backward_subs_resolution          true
% 7.94/1.51  --res_orphan_elimination                true
% 7.94/1.51  --res_time_limit                        2.
% 7.94/1.51  --res_out_proof                         true
% 7.94/1.51  
% 7.94/1.51  ------ Superposition Options
% 7.94/1.51  
% 7.94/1.51  --superposition_flag                    true
% 7.94/1.51  --sup_passive_queue_type                priority_queues
% 7.94/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.94/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.94/1.51  --demod_completeness_check              fast
% 7.94/1.51  --demod_use_ground                      true
% 7.94/1.51  --sup_to_prop_solver                    passive
% 7.94/1.51  --sup_prop_simpl_new                    true
% 7.94/1.51  --sup_prop_simpl_given                  true
% 7.94/1.51  --sup_fun_splitting                     false
% 7.94/1.51  --sup_smt_interval                      50000
% 7.94/1.51  
% 7.94/1.51  ------ Superposition Simplification Setup
% 7.94/1.51  
% 7.94/1.51  --sup_indices_passive                   []
% 7.94/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.94/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_full_bw                           [BwDemod]
% 7.94/1.51  --sup_immed_triv                        [TrivRules]
% 7.94/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_immed_bw_main                     []
% 7.94/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.94/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.51  
% 7.94/1.51  ------ Combination Options
% 7.94/1.51  
% 7.94/1.51  --comb_res_mult                         3
% 7.94/1.51  --comb_sup_mult                         2
% 7.94/1.51  --comb_inst_mult                        10
% 7.94/1.51  
% 7.94/1.51  ------ Debug Options
% 7.94/1.51  
% 7.94/1.51  --dbg_backtrace                         false
% 7.94/1.51  --dbg_dump_prop_clauses                 false
% 7.94/1.51  --dbg_dump_prop_clauses_file            -
% 7.94/1.51  --dbg_out_stat                          false
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  ------ Proving...
% 7.94/1.51  
% 7.94/1.51  
% 7.94/1.51  % SZS status Theorem for theBenchmark.p
% 7.94/1.51  
% 7.94/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.94/1.51  
% 7.94/1.51  fof(f22,conjecture,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f23,negated_conjecture,(
% 7.94/1.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.94/1.51    inference(negated_conjecture,[],[f22])).
% 7.94/1.51  
% 7.94/1.51  fof(f54,plain,(
% 7.94/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f23])).
% 7.94/1.51  
% 7.94/1.51  fof(f55,plain,(
% 7.94/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.94/1.51    inference(flattening,[],[f54])).
% 7.94/1.51  
% 7.94/1.51  fof(f61,plain,(
% 7.94/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.94/1.51    inference(nnf_transformation,[],[f55])).
% 7.94/1.51  
% 7.94/1.51  fof(f62,plain,(
% 7.94/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.94/1.51    inference(flattening,[],[f61])).
% 7.94/1.51  
% 7.94/1.51  fof(f66,plain,(
% 7.94/1.51    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK4 = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK4))) )),
% 7.94/1.51    introduced(choice_axiom,[])).
% 7.94/1.51  
% 7.94/1.51  fof(f65,plain,(
% 7.94/1.51    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK3,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK3,X0,X1)) & sK3 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 7.94/1.51    introduced(choice_axiom,[])).
% 7.94/1.51  
% 7.94/1.51  fof(f64,plain,(
% 7.94/1.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(X2,X0,sK2)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(X2,X0,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))) )),
% 7.94/1.51    introduced(choice_axiom,[])).
% 7.94/1.51  
% 7.94/1.51  fof(f63,plain,(
% 7.94/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK1,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK1,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 7.94/1.51    introduced(choice_axiom,[])).
% 7.94/1.51  
% 7.94/1.51  fof(f67,plain,(
% 7.94/1.51    ((((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)) & sK3 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 7.94/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f62,f66,f65,f64,f63])).
% 7.94/1.51  
% 7.94/1.51  fof(f108,plain,(
% 7.94/1.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f13,axiom,(
% 7.94/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f38,plain,(
% 7.94/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.51    inference(ennf_transformation,[],[f13])).
% 7.94/1.51  
% 7.94/1.51  fof(f39,plain,(
% 7.94/1.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.51    inference(flattening,[],[f38])).
% 7.94/1.51  
% 7.94/1.51  fof(f58,plain,(
% 7.94/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.51    inference(nnf_transformation,[],[f39])).
% 7.94/1.51  
% 7.94/1.51  fof(f80,plain,(
% 7.94/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.51    inference(cnf_transformation,[],[f58])).
% 7.94/1.51  
% 7.94/1.51  fof(f12,axiom,(
% 7.94/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f37,plain,(
% 7.94/1.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.51    inference(ennf_transformation,[],[f12])).
% 7.94/1.51  
% 7.94/1.51  fof(f79,plain,(
% 7.94/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.51    inference(cnf_transformation,[],[f37])).
% 7.94/1.51  
% 7.94/1.51  fof(f107,plain,(
% 7.94/1.51    v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f10,axiom,(
% 7.94/1.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f35,plain,(
% 7.94/1.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f10])).
% 7.94/1.51  
% 7.94/1.51  fof(f77,plain,(
% 7.94/1.51    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f35])).
% 7.94/1.51  
% 7.94/1.51  fof(f1,axiom,(
% 7.94/1.51    v1_xboole_0(k1_xboole_0)),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f68,plain,(
% 7.94/1.51    v1_xboole_0(k1_xboole_0)),
% 7.94/1.51    inference(cnf_transformation,[],[f1])).
% 7.94/1.51  
% 7.94/1.51  fof(f2,axiom,(
% 7.94/1.51    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f28,plain,(
% 7.94/1.51    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f2])).
% 7.94/1.51  
% 7.94/1.51  fof(f69,plain,(
% 7.94/1.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f28])).
% 7.94/1.51  
% 7.94/1.51  fof(f21,axiom,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f52,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f21])).
% 7.94/1.51  
% 7.94/1.51  fof(f53,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.94/1.51    inference(flattening,[],[f52])).
% 7.94/1.51  
% 7.94/1.51  fof(f60,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.94/1.51    inference(nnf_transformation,[],[f53])).
% 7.94/1.51  
% 7.94/1.51  fof(f98,plain,(
% 7.94/1.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f60])).
% 7.94/1.51  
% 7.94/1.51  fof(f119,plain,(
% 7.94/1.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.94/1.51    inference(equality_resolution,[],[f98])).
% 7.94/1.51  
% 7.94/1.51  fof(f99,plain,(
% 7.94/1.51    v2_pre_topc(sK1)),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f100,plain,(
% 7.94/1.51    l1_pre_topc(sK1)),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f101,plain,(
% 7.94/1.51    v2_pre_topc(sK2)),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f102,plain,(
% 7.94/1.51    l1_pre_topc(sK2)),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f106,plain,(
% 7.94/1.51    v1_funct_1(sK4)),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f105,plain,(
% 7.94/1.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f109,plain,(
% 7.94/1.51    sK3 = sK4),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f110,plain,(
% 7.94/1.51    v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f104,plain,(
% 7.94/1.51    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f18,axiom,(
% 7.94/1.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f47,plain,(
% 7.94/1.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f18])).
% 7.94/1.51  
% 7.94/1.51  fof(f93,plain,(
% 7.94/1.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f47])).
% 7.94/1.51  
% 7.94/1.51  fof(f19,axiom,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f24,plain,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.94/1.51    inference(pure_predicate_removal,[],[f19])).
% 7.94/1.51  
% 7.94/1.51  fof(f48,plain,(
% 7.94/1.51    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f24])).
% 7.94/1.51  
% 7.94/1.51  fof(f49,plain,(
% 7.94/1.51    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.94/1.51    inference(flattening,[],[f48])).
% 7.94/1.51  
% 7.94/1.51  fof(f94,plain,(
% 7.94/1.51    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f49])).
% 7.94/1.51  
% 7.94/1.51  fof(f17,axiom,(
% 7.94/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f25,plain,(
% 7.94/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.94/1.51    inference(pure_predicate_removal,[],[f17])).
% 7.94/1.51  
% 7.94/1.51  fof(f46,plain,(
% 7.94/1.51    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.94/1.51    inference(ennf_transformation,[],[f25])).
% 7.94/1.51  
% 7.94/1.51  fof(f92,plain,(
% 7.94/1.51    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.94/1.51    inference(cnf_transformation,[],[f46])).
% 7.94/1.51  
% 7.94/1.51  fof(f20,axiom,(
% 7.94/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f50,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.94/1.51    inference(ennf_transformation,[],[f20])).
% 7.94/1.51  
% 7.94/1.51  fof(f51,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.94/1.51    inference(flattening,[],[f50])).
% 7.94/1.51  
% 7.94/1.51  fof(f59,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.94/1.51    inference(nnf_transformation,[],[f51])).
% 7.94/1.51  
% 7.94/1.51  fof(f95,plain,(
% 7.94/1.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f59])).
% 7.94/1.51  
% 7.94/1.51  fof(f118,plain,(
% 7.94/1.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.94/1.51    inference(equality_resolution,[],[f95])).
% 7.94/1.51  
% 7.94/1.51  fof(f97,plain,(
% 7.94/1.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f60])).
% 7.94/1.51  
% 7.94/1.51  fof(f120,plain,(
% 7.94/1.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.94/1.51    inference(equality_resolution,[],[f97])).
% 7.94/1.51  
% 7.94/1.51  fof(f111,plain,(
% 7.94/1.51    ~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)),
% 7.94/1.51    inference(cnf_transformation,[],[f67])).
% 7.94/1.51  
% 7.94/1.51  fof(f96,plain,(
% 7.94/1.51    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f59])).
% 7.94/1.51  
% 7.94/1.51  fof(f117,plain,(
% 7.94/1.51    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.94/1.51    inference(equality_resolution,[],[f96])).
% 7.94/1.51  
% 7.94/1.51  fof(f4,axiom,(
% 7.94/1.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f72,plain,(
% 7.94/1.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.94/1.51    inference(cnf_transformation,[],[f4])).
% 7.94/1.51  
% 7.94/1.51  fof(f81,plain,(
% 7.94/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.51    inference(cnf_transformation,[],[f58])).
% 7.94/1.51  
% 7.94/1.51  fof(f116,plain,(
% 7.94/1.51    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.94/1.51    inference(equality_resolution,[],[f81])).
% 7.94/1.51  
% 7.94/1.51  fof(f83,plain,(
% 7.94/1.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.51    inference(cnf_transformation,[],[f58])).
% 7.94/1.51  
% 7.94/1.51  fof(f115,plain,(
% 7.94/1.51    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.94/1.51    inference(equality_resolution,[],[f83])).
% 7.94/1.51  
% 7.94/1.51  fof(f11,axiom,(
% 7.94/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f36,plain,(
% 7.94/1.51    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.94/1.51    inference(ennf_transformation,[],[f11])).
% 7.94/1.51  
% 7.94/1.51  fof(f78,plain,(
% 7.94/1.51    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.94/1.51    inference(cnf_transformation,[],[f36])).
% 7.94/1.51  
% 7.94/1.51  fof(f5,axiom,(
% 7.94/1.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.94/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.51  
% 7.94/1.51  fof(f30,plain,(
% 7.94/1.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.94/1.51    inference(ennf_transformation,[],[f5])).
% 7.94/1.51  
% 7.94/1.51  fof(f73,plain,(
% 7.94/1.51    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.94/1.51    inference(cnf_transformation,[],[f30])).
% 7.94/1.51  
% 7.94/1.51  cnf(c_34,negated_conjecture,
% 7.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
% 7.94/1.51      inference(cnf_transformation,[],[f108]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1794,plain,
% 7.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_17,plain,
% 7.94/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.51      | k1_relset_1(X1,X2,X0) = X1
% 7.94/1.51      | k1_xboole_0 = X2 ),
% 7.94/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1808,plain,
% 7.94/1.51      ( k1_relset_1(X0,X1,X2) = X0
% 7.94/1.51      | k1_xboole_0 = X1
% 7.94/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.94/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6680,plain,
% 7.94/1.51      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK4) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.94/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1794,c_1808]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_11,plain,
% 7.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f79]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1814,plain,
% 7.94/1.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.94/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3799,plain,
% 7.94/1.51      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK4) = k1_relat_1(sK4) ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1794,c_1814]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6692,plain,
% 7.94/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 7.94/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
% 7.94/1.51      inference(light_normalisation,[status(thm)],[c_6680,c_3799]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_35,negated_conjecture,
% 7.94/1.51      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
% 7.94/1.51      inference(cnf_transformation,[],[f107]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6733,plain,
% 7.94/1.51      ( ~ v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
% 7.94/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 7.94/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4) ),
% 7.94/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_6692]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8976,plain,
% 7.94/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
% 7.94/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0 ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_6692,c_35,c_6733]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8977,plain,
% 7.94/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 7.94/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4) ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_8976]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9,plain,
% 7.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.51      | ~ v1_xboole_0(X2)
% 7.94/1.51      | v1_xboole_0(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1816,plain,
% 7.94/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.94/1.51      | v1_xboole_0(X2) != iProver_top
% 7.94/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_4952,plain,
% 7.94/1.51      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1794,c_1816]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_9007,plain,
% 7.94/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
% 7.94/1.51      | v1_xboole_0(sK4) = iProver_top
% 7.94/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_8977,c_4952]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_0,plain,
% 7.94/1.51      ( v1_xboole_0(k1_xboole_0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_138,plain,
% 7.94/1.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_11613,plain,
% 7.94/1.51      ( v1_xboole_0(sK4) = iProver_top
% 7.94/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_9007,c_138]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_11614,plain,
% 7.94/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
% 7.94/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_11613]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1822,plain,
% 7.94/1.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1,plain,
% 7.94/1.51      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 7.94/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1821,plain,
% 7.94/1.51      ( X0 = X1
% 7.94/1.51      | v1_xboole_0(X1) != iProver_top
% 7.94/1.51      | v1_xboole_0(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3595,plain,
% 7.94/1.51      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1822,c_1821]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_11620,plain,
% 7.94/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
% 7.94/1.51      | sK4 = k1_xboole_0 ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_11614,c_3595]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_29,plain,
% 7.94/1.51      ( v5_pre_topc(X0,X1,X2)
% 7.94/1.51      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ v2_pre_topc(X2)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | ~ l1_pre_topc(X2)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f119]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1798,plain,
% 7.94/1.51      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.94/1.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 7.94/1.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.94/1.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.94/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.94/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.94/1.51      | v2_pre_topc(X1) != iProver_top
% 7.94/1.51      | v2_pre_topc(X2) != iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top
% 7.94/1.51      | l1_pre_topc(X2) != iProver_top
% 7.94/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_4704,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1794,c_1798]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_43,negated_conjecture,
% 7.94/1.51      ( v2_pre_topc(sK1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f99]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_44,plain,
% 7.94/1.51      ( v2_pre_topc(sK1) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_42,negated_conjecture,
% 7.94/1.51      ( l1_pre_topc(sK1) ),
% 7.94/1.51      inference(cnf_transformation,[],[f100]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_45,plain,
% 7.94/1.51      ( l1_pre_topc(sK1) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_41,negated_conjecture,
% 7.94/1.51      ( v2_pre_topc(sK2) ),
% 7.94/1.51      inference(cnf_transformation,[],[f101]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_46,plain,
% 7.94/1.51      ( v2_pre_topc(sK2) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_40,negated_conjecture,
% 7.94/1.51      ( l1_pre_topc(sK2) ),
% 7.94/1.51      inference(cnf_transformation,[],[f102]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_47,plain,
% 7.94/1.51      ( l1_pre_topc(sK2) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_36,negated_conjecture,
% 7.94/1.51      ( v1_funct_1(sK4) ),
% 7.94/1.51      inference(cnf_transformation,[],[f106]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_51,plain,
% 7.94/1.51      ( v1_funct_1(sK4) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_52,plain,
% 7.94/1.51      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_37,negated_conjecture,
% 7.94/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 7.94/1.51      inference(cnf_transformation,[],[f105]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1791,plain,
% 7.94/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_33,negated_conjecture,
% 7.94/1.51      ( sK3 = sK4 ),
% 7.94/1.51      inference(cnf_transformation,[],[f109]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1843,plain,
% 7.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 7.94/1.51      inference(light_normalisation,[status(thm)],[c_1791,c_33]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_32,negated_conjecture,
% 7.94/1.51      ( v5_pre_topc(sK3,sK1,sK2)
% 7.94/1.51      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 7.94/1.51      inference(cnf_transformation,[],[f110]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1795,plain,
% 7.94/1.51      ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1908,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,sK1,sK2) = iProver_top ),
% 7.94/1.51      inference(light_normalisation,[status(thm)],[c_1795,c_33]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_38,negated_conjecture,
% 7.94/1.51      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 7.94/1.51      inference(cnf_transformation,[],[f104]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1790,plain,
% 7.94/1.51      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1840,plain,
% 7.94/1.51      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 7.94/1.51      inference(light_normalisation,[status(thm)],[c_1790,c_33]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_25,plain,
% 7.94/1.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.94/1.51      | ~ l1_pre_topc(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2158,plain,
% 7.94/1.51      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.94/1.51      | ~ l1_pre_topc(sK1) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_25]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2159,plain,
% 7.94/1.51      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_2158]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_26,plain,
% 7.94/1.51      ( ~ v2_pre_topc(X0)
% 7.94/1.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.94/1.51      | ~ l1_pre_topc(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2176,plain,
% 7.94/1.51      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(sK1) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_26]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2177,plain,
% 7.94/1.51      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.94/1.51      | v2_pre_topc(sK1) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_2176]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_24,plain,
% 7.94/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.94/1.51      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.94/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2377,plain,
% 7.94/1.51      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.94/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_24]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2378,plain,
% 7.94/1.51      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 7.94/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_2377]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_28,plain,
% 7.94/1.51      ( ~ v5_pre_topc(X0,X1,X2)
% 7.94/1.51      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ v2_pre_topc(X2)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | ~ l1_pre_topc(X2)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f118]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2344,plain,
% 7.94/1.51      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
% 7.94/1.51      | ~ v5_pre_topc(X0,sK1,X1)
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_28]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2820,plain,
% 7.94/1.51      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
% 7.94/1.51      | ~ v5_pre_topc(X0,sK1,sK2)
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_2344]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3518,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
% 7.94/1.51      | ~ v5_pre_topc(sK4,sK1,sK2)
% 7.94/1.51      | ~ v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
% 7.94/1.51      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
% 7.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(sK4) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_2820]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3519,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,sK1,sK2) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK1) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.94/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_3518]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_30,plain,
% 7.94/1.51      ( ~ v5_pre_topc(X0,X1,X2)
% 7.94/1.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ v2_pre_topc(X2)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | ~ l1_pre_topc(X2)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f120]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1797,plain,
% 7.94/1.51      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.94/1.51      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 7.94/1.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.94/1.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.94/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.94/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.94/1.51      | v2_pre_topc(X1) != iProver_top
% 7.94/1.51      | v2_pre_topc(X2) != iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top
% 7.94/1.51      | l1_pre_topc(X2) != iProver_top
% 7.94/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3330,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1794,c_1797]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_31,negated_conjecture,
% 7.94/1.51      ( ~ v5_pre_topc(sK3,sK1,sK2)
% 7.94/1.51      | ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 7.94/1.51      inference(cnf_transformation,[],[f111]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1796,plain,
% 7.94/1.51      ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1913,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,sK1,sK2) != iProver_top ),
% 7.94/1.51      inference(light_normalisation,[status(thm)],[c_1796,c_33]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_27,plain,
% 7.94/1.51      ( v5_pre_topc(X0,X1,X2)
% 7.94/1.51      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ v2_pre_topc(X2)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | ~ l1_pre_topc(X2)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(cnf_transformation,[],[f117]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2334,plain,
% 7.94/1.51      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X1)
% 7.94/1.51      | v5_pre_topc(X0,sK1,X1)
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X1))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_27]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2774,plain,
% 7.94/1.51      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
% 7.94/1.51      | v5_pre_topc(X0,sK1,sK2)
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_2334]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3454,plain,
% 7.94/1.51      ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
% 7.94/1.51      | v5_pre_topc(sK4,sK1,sK2)
% 7.94/1.51      | ~ v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
% 7.94/1.51      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
% 7.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(sK4) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_2774]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3455,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK1) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.94/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_3454]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3941,plain,
% 7.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_3330,c_44,c_45,c_46,c_47,c_51,c_52,c_1843,c_1913,
% 7.94/1.51                 c_1840,c_2159,c_2177,c_2378,c_3455]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3942,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_3941]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_5046,plain,
% 7.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_4704,c_44,c_45,c_46,c_47,c_51,c_52,c_1843,c_1908,
% 7.94/1.51                 c_1840,c_2159,c_2177,c_2378,c_3519,c_3942]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_5047,plain,
% 7.94/1.51      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_5046]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_26054,plain,
% 7.94/1.51      ( sK4 = k1_xboole_0
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(sK2)))) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_11620,c_5047]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1793,plain,
% 7.94/1.51      ( v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_26060,plain,
% 7.94/1.51      ( sK4 = k1_xboole_0
% 7.94/1.51      | v1_funct_2(sK4,k1_relat_1(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_11620,c_1793]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6681,plain,
% 7.94/1.51      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4) = u1_struct_0(sK1)
% 7.94/1.51      | u1_struct_0(sK2) = k1_xboole_0
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1843,c_1808]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3800,plain,
% 7.94/1.51      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK4) = k1_relat_1(sK4) ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1843,c_1814]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6685,plain,
% 7.94/1.51      ( u1_struct_0(sK2) = k1_xboole_0
% 7.94/1.51      | u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 7.94/1.51      inference(light_normalisation,[status(thm)],[c_6681,c_3800]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7187,plain,
% 7.94/1.51      ( u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.51      | u1_struct_0(sK2) = k1_xboole_0 ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_6685,c_1840]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7188,plain,
% 7.94/1.51      ( u1_struct_0(sK2) = k1_xboole_0
% 7.94/1.51      | u1_struct_0(sK1) = k1_relat_1(sK4) ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_7187]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_4953,plain,
% 7.94/1.51      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1843,c_1816]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_7212,plain,
% 7.94/1.51      ( u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.51      | v1_xboole_0(sK4) = iProver_top
% 7.94/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_7188,c_4953]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8502,plain,
% 7.94/1.51      ( v1_xboole_0(sK4) = iProver_top
% 7.94/1.51      | u1_struct_0(sK1) = k1_relat_1(sK4) ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_7212,c_138]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8503,plain,
% 7.94/1.51      ( u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.94/1.51      inference(renaming,[status(thm)],[c_8502]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_8508,plain,
% 7.94/1.51      ( u1_struct_0(sK1) = k1_relat_1(sK4) | sK4 = k1_xboole_0 ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_8503,c_3595]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_26059,plain,
% 7.94/1.51      ( sK4 = k1_xboole_0
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) = iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_11620,c_1794]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1800,plain,
% 7.94/1.51      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.94/1.51      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 7.94/1.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.94/1.51      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.94/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.94/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.94/1.51      | v2_pre_topc(X1) != iProver_top
% 7.94/1.51      | v2_pre_topc(X2) != iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top
% 7.94/1.51      | l1_pre_topc(X2) != iProver_top
% 7.94/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_6255,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
% 7.94/1.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK1) != iProver_top
% 7.94/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.94/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1794,c_1800]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2155,plain,
% 7.94/1.51      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.94/1.51      | ~ l1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_25]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2156,plain,
% 7.94/1.51      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_2155]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2173,plain,
% 7.94/1.51      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK2) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_26]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2174,plain,
% 7.94/1.51      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_2173]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2369,plain,
% 7.94/1.51      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.94/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_24]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2370,plain,
% 7.94/1.51      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_2369]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2364,plain,
% 7.94/1.51      ( ~ v5_pre_topc(X0,sK1,X1)
% 7.94/1.51      | v5_pre_topc(X0,sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_30]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2900,plain,
% 7.94/1.51      ( v5_pre_topc(X0,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.94/1.51      | ~ v5_pre_topc(X0,sK1,sK2)
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_2364]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3677,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.94/1.51      | ~ v5_pre_topc(sK4,sK1,sK2)
% 7.94/1.51      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
% 7.94/1.51      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
% 7.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(sK4) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_2900]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3678,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,sK1,sK2) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK1) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.94/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_3677]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_1799,plain,
% 7.94/1.51      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.94/1.51      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 7.94/1.51      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.94/1.51      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.94/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.94/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.94/1.51      | v2_pre_topc(X1) != iProver_top
% 7.94/1.51      | v2_pre_topc(X2) != iProver_top
% 7.94/1.51      | l1_pre_topc(X1) != iProver_top
% 7.94/1.51      | l1_pre_topc(X2) != iProver_top
% 7.94/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_5112,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
% 7.94/1.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK1) != iProver_top
% 7.94/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.94/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.51      inference(superposition,[status(thm)],[c_1794,c_1799]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2354,plain,
% 7.94/1.51      ( v5_pre_topc(X0,sK1,X1)
% 7.94/1.51      | ~ v5_pre_topc(X0,sK1,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 7.94/1.51      | ~ v2_pre_topc(X1)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(X1)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_29]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_2860,plain,
% 7.94/1.51      ( ~ v5_pre_topc(X0,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.94/1.51      | v5_pre_topc(X0,sK1,sK2)
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
% 7.94/1.51      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
% 7.94/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(X0) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_2354]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3613,plain,
% 7.94/1.51      ( ~ v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.94/1.51      | v5_pre_topc(sK4,sK1,sK2)
% 7.94/1.51      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
% 7.94/1.51      | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
% 7.94/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.94/1.51      | ~ v2_pre_topc(sK2)
% 7.94/1.51      | ~ v2_pre_topc(sK1)
% 7.94/1.51      | ~ l1_pre_topc(sK2)
% 7.94/1.51      | ~ l1_pre_topc(sK1)
% 7.94/1.51      | ~ v1_funct_1(sK4) ),
% 7.94/1.51      inference(instantiation,[status(thm)],[c_2860]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_3614,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,sK1,sK2) = iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
% 7.94/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.94/1.51      | v2_pre_topc(sK1) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.94/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.94/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.94/1.51      inference(predicate_to_equality,[status(thm)],[c_3613]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_5798,plain,
% 7.94/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.51      | v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 7.94/1.51      inference(global_propositional_subsumption,
% 7.94/1.51                [status(thm)],
% 7.94/1.51                [c_5112,c_44,c_45,c_46,c_47,c_51,c_52,c_1843,c_1913,
% 7.94/1.51                 c_1840,c_2156,c_2174,c_2370,c_3614]) ).
% 7.94/1.51  
% 7.94/1.51  cnf(c_5799,plain,
% 7.94/1.51      ( v5_pre_topc(sK4,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.94/1.51      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_5798]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_6742,plain,
% 7.94/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_6255,c_44,c_45,c_46,c_47,c_51,c_52,c_1843,c_1908,
% 7.94/1.52                 c_1840,c_2156,c_2174,c_2370,c_3678,c_5799]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_6743,plain,
% 7.94/1.52      ( v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_6742]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_20640,plain,
% 7.94/1.52      ( sK4 = k1_xboole_0
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_8508,c_6743]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27267,plain,
% 7.94/1.52      ( sK4 = k1_xboole_0
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_26059,c_20640]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27301,plain,
% 7.94/1.52      ( sK4 = k1_xboole_0
% 7.94/1.52      | v1_funct_2(sK4,k1_relat_1(sK4),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_8508,c_27267]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27491,plain,
% 7.94/1.52      ( sK4 = k1_xboole_0 ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_26054,c_26060,c_27301]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27607,plain,
% 7.94/1.52      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_27491,c_3799]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4,plain,
% 7.94/1.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1818,plain,
% 7.94/1.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_16,plain,
% 7.94/1.52      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.94/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.94/1.52      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.94/1.52      inference(cnf_transformation,[],[f116]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1809,plain,
% 7.94/1.52      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.94/1.52      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5260,plain,
% 7.94/1.52      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0
% 7.94/1.52      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_1818,c_1809]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_3798,plain,
% 7.94/1.52      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_1818,c_1814]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5270,plain,
% 7.94/1.52      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 7.94/1.52      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) != iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_5260,c_3798]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_14,plain,
% 7.94/1.52      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.94/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.94/1.52      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.94/1.52      inference(cnf_transformation,[],[f115]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_100,plain,
% 7.94/1.52      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 7.94/1.52      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 7.94/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_102,plain,
% 7.94/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.94/1.52      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 7.94/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_100]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_2214,plain,
% 7.94/1.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_2217,plain,
% 7.94/1.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_2214]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_2219,plain,
% 7.94/1.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_2217]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_3923,plain,
% 7.94/1.52      ( ~ v1_xboole_0(k1_relset_1(k1_xboole_0,X0,X1))
% 7.94/1.52      | ~ v1_xboole_0(k1_xboole_0)
% 7.94/1.52      | k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_3924,plain,
% 7.94/1.52      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.94/1.52      | v1_xboole_0(k1_relset_1(k1_xboole_0,X0,X1)) != iProver_top
% 7.94/1.52      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_3923]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_3926,plain,
% 7.94/1.52      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 7.94/1.52      | v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.94/1.52      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_3924]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_10,plain,
% 7.94/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.94/1.52      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.94/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1815,plain,
% 7.94/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.94/1.52      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5,plain,
% 7.94/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.94/1.52      | ~ v1_xboole_0(X1)
% 7.94/1.52      | v1_xboole_0(X0) ),
% 7.94/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_1817,plain,
% 7.94/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.94/1.52      | v1_xboole_0(X1) != iProver_top
% 7.94/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4808,plain,
% 7.94/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.94/1.52      | v1_xboole_0(X1) != iProver_top
% 7.94/1.52      | v1_xboole_0(k1_relset_1(X1,X2,X0)) = iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_1815,c_1817]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_4894,plain,
% 7.94/1.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.94/1.52      | v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = iProver_top
% 7.94/1.52      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_4808]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5286,plain,
% 7.94/1.52      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 7.94/1.52      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_5270]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_6041,plain,
% 7.94/1.52      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_5270,c_102,c_138,c_2219,c_3926,c_4894,c_5286]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27643,plain,
% 7.94/1.52      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = k1_xboole_0 ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_27607,c_6041]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27614,plain,
% 7.94/1.52      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_27491,c_1793]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_6677,plain,
% 7.94/1.52      ( k1_relset_1(X0,X1,k1_xboole_0) = X0
% 7.94/1.52      | k1_xboole_0 = X1
% 7.94/1.52      | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_1818,c_1808]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_28263,plain,
% 7.94/1.52      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 7.94/1.52      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0 ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_27614,c_6677]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_136,plain,
% 7.94/1.52      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_901,plain,
% 7.94/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.94/1.52      | v1_funct_2(X3,X4,X5)
% 7.94/1.52      | X3 != X0
% 7.94/1.52      | X4 != X1
% 7.94/1.52      | X5 != X2 ),
% 7.94/1.52      theory(equality) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_13965,plain,
% 7.94/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.94/1.52      | v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
% 7.94/1.52      | X3 != X0
% 7.94/1.52      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != X2
% 7.94/1.52      | u1_struct_0(sK1) != X1 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_901]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_13966,plain,
% 7.94/1.52      ( X0 != X1
% 7.94/1.52      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != X2
% 7.94/1.52      | u1_struct_0(sK1) != X3
% 7.94/1.52      | v1_funct_2(X1,X3,X2) != iProver_top
% 7.94/1.52      | v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_13965]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_13968,plain,
% 7.94/1.52      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != k1_xboole_0
% 7.94/1.52      | u1_struct_0(sK1) != k1_xboole_0
% 7.94/1.52      | k1_xboole_0 != k1_xboole_0
% 7.94/1.52      | v1_funct_2(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = iProver_top
% 7.94/1.52      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_13966]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9009,plain,
% 7.94/1.52      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0))) = iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_8977,c_1794]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_7208,plain,
% 7.94/1.52      ( u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0))) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_7188,c_5047]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_11299,plain,
% 7.94/1.52      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
% 7.94/1.52      | u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_9009,c_7208]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_7220,plain,
% 7.94/1.52      ( u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) = iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_7188,c_1843]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_7221,plain,
% 7.94/1.52      ( u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK1),k1_xboole_0) = iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_7188,c_1840]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9003,plain,
% 7.94/1.52      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_8977,c_6743]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_11329,plain,
% 7.94/1.52      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(sK1),k1_xboole_0) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_8977,c_9003]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_12292,plain,
% 7.94/1.52      ( u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.52      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4) ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_11299,c_7220,c_7221,c_11329]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_12293,plain,
% 7.94/1.52      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_relat_1(sK4)
% 7.94/1.52      | u1_struct_0(sK1) = k1_relat_1(sK4) ),
% 7.94/1.52      inference(renaming,[status(thm)],[c_12292]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_12335,plain,
% 7.94/1.52      ( u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_12293,c_7208]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_18618,plain,
% 7.94/1.52      ( u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.52      | v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_7188,c_12335]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_19549,plain,
% 7.94/1.52      ( u1_struct_0(sK1) = k1_relat_1(sK4)
% 7.94/1.52      | v1_funct_2(sK4,k1_relat_1(sK4),k1_xboole_0) != iProver_top
% 7.94/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) != iProver_top ),
% 7.94/1.52      inference(superposition,[status(thm)],[c_12293,c_18618]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27521,plain,
% 7.94/1.52      ( u1_struct_0(sK1) = k1_relat_1(k1_xboole_0)
% 7.94/1.52      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 7.94/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) != iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_27491,c_19549]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27981,plain,
% 7.94/1.52      ( u1_struct_0(sK1) = k1_xboole_0
% 7.94/1.52      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 7.94/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.94/1.52      inference(light_normalisation,[status(thm)],[c_27521,c_6041]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27592,plain,
% 7.94/1.52      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top
% 7.94/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) != iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_27491,c_6743]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_28479,plain,
% 7.94/1.52      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != iProver_top ),
% 7.94/1.52      inference(forward_subsumption_resolution,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_27592,c_1818]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_29423,plain,
% 7.94/1.52      ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 7.94/1.52      inference(global_propositional_subsumption,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_28263,c_102,c_136,c_0,c_138,c_2219,c_3926,c_4894,
% 7.94/1.52                 c_13968,c_27981,c_28479]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_30109,plain,
% 7.94/1.52      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = k1_xboole_0 ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_27643,c_29423]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_27601,plain,
% 7.94/1.52      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top
% 7.94/1.52      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) != iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_27491,c_5047]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_28484,plain,
% 7.94/1.52      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) != iProver_top ),
% 7.94/1.52      inference(forward_subsumption_resolution,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_27601,c_1818]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_30118,plain,
% 7.94/1.52      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK2)) != iProver_top ),
% 7.94/1.52      inference(demodulation,[status(thm)],[c_30109,c_28484]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_895,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_2508,plain,
% 7.94/1.52      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_895]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_13335,plain,
% 7.94/1.52      ( X0 = sK3 | X0 != sK4 | sK3 != sK4 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_2508]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_13336,plain,
% 7.94/1.52      ( sK3 != sK4 | k1_xboole_0 = sK3 | k1_xboole_0 != sK4 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_13335]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9769,plain,
% 7.94/1.52      ( X0 != X1 | X0 = u1_struct_0(sK1) | u1_struct_0(sK1) != X1 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_895]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_9770,plain,
% 7.94/1.52      ( u1_struct_0(sK1) != k1_xboole_0
% 7.94/1.52      | k1_xboole_0 = u1_struct_0(sK1)
% 7.94/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_9769]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_894,plain,( X0 = X0 ),theory(equality) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5756,plain,
% 7.94/1.52      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_894]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_2313,plain,
% 7.94/1.52      ( v1_funct_2(X0,X1,X2)
% 7.94/1.52      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.94/1.52      | X2 != u1_struct_0(sK2)
% 7.94/1.52      | X1 != u1_struct_0(sK1)
% 7.94/1.52      | X0 != sK3 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_901]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5755,plain,
% 7.94/1.52      ( v1_funct_2(X0,X1,u1_struct_0(sK2))
% 7.94/1.52      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.94/1.52      | X1 != u1_struct_0(sK1)
% 7.94/1.52      | X0 != sK3
% 7.94/1.52      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_2313]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5757,plain,
% 7.94/1.52      ( X0 != u1_struct_0(sK1)
% 7.94/1.52      | X1 != sK3
% 7.94/1.52      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 7.94/1.52      | v1_funct_2(X1,X0,u1_struct_0(sK2)) = iProver_top
% 7.94/1.52      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_5755]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_5759,plain,
% 7.94/1.52      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 7.94/1.52      | k1_xboole_0 != u1_struct_0(sK1)
% 7.94/1.52      | k1_xboole_0 != sK3
% 7.94/1.52      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 7.94/1.52      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK2)) = iProver_top ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_5757]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_2489,plain,
% 7.94/1.52      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_895]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_2490,plain,
% 7.94/1.52      ( sK4 != k1_xboole_0
% 7.94/1.52      | k1_xboole_0 = sK4
% 7.94/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.94/1.52      inference(instantiation,[status(thm)],[c_2489]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(c_49,plain,
% 7.94/1.52      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 7.94/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.94/1.52  
% 7.94/1.52  cnf(contradiction,plain,
% 7.94/1.52      ( $false ),
% 7.94/1.52      inference(minisat,
% 7.94/1.52                [status(thm)],
% 7.94/1.52                [c_30118,c_27981,c_27491,c_13336,c_9770,c_5756,c_5759,
% 7.94/1.52                 c_4894,c_3926,c_2490,c_2219,c_138,c_0,c_136,c_102,c_33,
% 7.94/1.52                 c_49]) ).
% 7.94/1.52  
% 7.94/1.52  
% 7.94/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.94/1.52  
% 7.94/1.52  ------                               Statistics
% 7.94/1.52  
% 7.94/1.52  ------ General
% 7.94/1.52  
% 7.94/1.52  abstr_ref_over_cycles:                  0
% 7.94/1.52  abstr_ref_under_cycles:                 0
% 7.94/1.52  gc_basic_clause_elim:                   0
% 7.94/1.52  forced_gc_time:                         0
% 7.94/1.52  parsing_time:                           0.008
% 7.94/1.52  unif_index_cands_time:                  0.
% 7.94/1.52  unif_index_add_time:                    0.
% 7.94/1.52  orderings_time:                         0.
% 7.94/1.52  out_proof_time:                         0.022
% 7.94/1.52  total_time:                             0.873
% 7.94/1.52  num_of_symbols:                         55
% 7.94/1.52  num_of_terms:                           26109
% 7.94/1.52  
% 7.94/1.52  ------ Preprocessing
% 7.94/1.52  
% 7.94/1.52  num_of_splits:                          0
% 7.94/1.52  num_of_split_atoms:                     0
% 7.94/1.52  num_of_reused_defs:                     0
% 7.94/1.52  num_eq_ax_congr_red:                    33
% 7.94/1.52  num_of_sem_filtered_clauses:            1
% 7.94/1.52  num_of_subtypes:                        0
% 7.94/1.52  monotx_restored_types:                  0
% 7.94/1.52  sat_num_of_epr_types:                   0
% 7.94/1.52  sat_num_of_non_cyclic_types:            0
% 7.94/1.52  sat_guarded_non_collapsed_types:        0
% 7.94/1.52  num_pure_diseq_elim:                    0
% 7.94/1.52  simp_replaced_by:                       0
% 7.94/1.52  res_preprocessed:                       193
% 7.94/1.52  prep_upred:                             0
% 7.94/1.52  prep_unflattend:                        0
% 7.94/1.52  smt_new_axioms:                         0
% 7.94/1.52  pred_elim_cands:                        7
% 7.94/1.52  pred_elim:                              2
% 7.94/1.52  pred_elim_cl:                           2
% 7.94/1.52  pred_elim_cycles:                       4
% 7.94/1.52  merged_defs:                            8
% 7.94/1.52  merged_defs_ncl:                        0
% 7.94/1.52  bin_hyper_res:                          8
% 7.94/1.52  prep_cycles:                            4
% 7.94/1.52  pred_elim_time:                         0.002
% 7.94/1.52  splitting_time:                         0.
% 7.94/1.52  sem_filter_time:                        0.
% 7.94/1.52  monotx_time:                            0.
% 7.94/1.52  subtype_inf_time:                       0.
% 7.94/1.52  
% 7.94/1.52  ------ Problem properties
% 7.94/1.52  
% 7.94/1.52  clauses:                                40
% 7.94/1.52  conjectures:                            13
% 7.94/1.52  epr:                                    9
% 7.94/1.52  horn:                                   34
% 7.94/1.52  ground:                                 14
% 7.94/1.52  unary:                                  13
% 7.94/1.52  binary:                                 9
% 7.94/1.52  lits:                                   121
% 7.94/1.52  lits_eq:                                15
% 7.94/1.52  fd_pure:                                0
% 7.94/1.52  fd_pseudo:                              0
% 7.94/1.52  fd_cond:                                3
% 7.94/1.52  fd_pseudo_cond:                         1
% 7.94/1.52  ac_symbols:                             0
% 7.94/1.52  
% 7.94/1.52  ------ Propositional Solver
% 7.94/1.52  
% 7.94/1.52  prop_solver_calls:                      27
% 7.94/1.52  prop_fast_solver_calls:                 2167
% 7.94/1.52  smt_solver_calls:                       0
% 7.94/1.52  smt_fast_solver_calls:                  0
% 7.94/1.52  prop_num_of_clauses:                    9633
% 7.94/1.52  prop_preprocess_simplified:             18751
% 7.94/1.52  prop_fo_subsumed:                       158
% 7.94/1.52  prop_solver_time:                       0.
% 7.94/1.52  smt_solver_time:                        0.
% 7.94/1.52  smt_fast_solver_time:                   0.
% 7.94/1.52  prop_fast_solver_time:                  0.
% 7.94/1.52  prop_unsat_core_time:                   0.001
% 7.94/1.52  
% 7.94/1.52  ------ QBF
% 7.94/1.52  
% 7.94/1.52  qbf_q_res:                              0
% 7.94/1.52  qbf_num_tautologies:                    0
% 7.94/1.52  qbf_prep_cycles:                        0
% 7.94/1.52  
% 7.94/1.52  ------ BMC1
% 7.94/1.52  
% 7.94/1.52  bmc1_current_bound:                     -1
% 7.94/1.52  bmc1_last_solved_bound:                 -1
% 7.94/1.52  bmc1_unsat_core_size:                   -1
% 7.94/1.52  bmc1_unsat_core_parents_size:           -1
% 7.94/1.52  bmc1_merge_next_fun:                    0
% 7.94/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.94/1.52  
% 7.94/1.52  ------ Instantiation
% 7.94/1.52  
% 7.94/1.52  inst_num_of_clauses:                    2467
% 7.94/1.52  inst_num_in_passive:                    978
% 7.94/1.52  inst_num_in_active:                     947
% 7.94/1.52  inst_num_in_unprocessed:                542
% 7.94/1.52  inst_num_of_loops:                      1270
% 7.94/1.52  inst_num_of_learning_restarts:          0
% 7.94/1.52  inst_num_moves_active_passive:          322
% 7.94/1.52  inst_lit_activity:                      0
% 7.94/1.52  inst_lit_activity_moves:                0
% 7.94/1.52  inst_num_tautologies:                   0
% 7.94/1.52  inst_num_prop_implied:                  0
% 7.94/1.52  inst_num_existing_simplified:           0
% 7.94/1.52  inst_num_eq_res_simplified:             0
% 7.94/1.52  inst_num_child_elim:                    0
% 7.94/1.52  inst_num_of_dismatching_blockings:      1459
% 7.94/1.52  inst_num_of_non_proper_insts:           2029
% 7.94/1.52  inst_num_of_duplicates:                 0
% 7.94/1.52  inst_inst_num_from_inst_to_res:         0
% 7.94/1.52  inst_dismatching_checking_time:         0.
% 7.94/1.52  
% 7.94/1.52  ------ Resolution
% 7.94/1.52  
% 7.94/1.52  res_num_of_clauses:                     0
% 7.94/1.52  res_num_in_passive:                     0
% 7.94/1.52  res_num_in_active:                      0
% 7.94/1.52  res_num_of_loops:                       197
% 7.94/1.52  res_forward_subset_subsumed:            59
% 7.94/1.52  res_backward_subset_subsumed:           0
% 7.94/1.52  res_forward_subsumed:                   0
% 7.94/1.52  res_backward_subsumed:                  0
% 7.94/1.52  res_forward_subsumption_resolution:     0
% 7.94/1.52  res_backward_subsumption_resolution:    0
% 7.94/1.52  res_clause_to_clause_subsumption:       1973
% 7.94/1.52  res_orphan_elimination:                 0
% 7.94/1.52  res_tautology_del:                      76
% 7.94/1.52  res_num_eq_res_simplified:              0
% 7.94/1.52  res_num_sel_changes:                    0
% 7.94/1.52  res_moves_from_active_to_pass:          0
% 7.94/1.52  
% 7.94/1.52  ------ Superposition
% 7.94/1.52  
% 7.94/1.52  sup_time_total:                         0.
% 7.94/1.52  sup_time_generating:                    0.
% 7.94/1.52  sup_time_sim_full:                      0.
% 7.94/1.52  sup_time_sim_immed:                     0.
% 7.94/1.52  
% 7.94/1.52  sup_num_of_clauses:                     546
% 7.94/1.52  sup_num_in_active:                      93
% 7.94/1.52  sup_num_in_passive:                     453
% 7.94/1.52  sup_num_of_loops:                       253
% 7.94/1.52  sup_fw_superposition:                   530
% 7.94/1.52  sup_bw_superposition:                   705
% 7.94/1.52  sup_immediate_simplified:               391
% 7.94/1.52  sup_given_eliminated:                   3
% 7.94/1.52  comparisons_done:                       0
% 7.94/1.52  comparisons_avoided:                    78
% 7.94/1.52  
% 7.94/1.52  ------ Simplifications
% 7.94/1.52  
% 7.94/1.52  
% 7.94/1.52  sim_fw_subset_subsumed:                 178
% 7.94/1.52  sim_bw_subset_subsumed:                 130
% 7.94/1.52  sim_fw_subsumed:                        54
% 7.94/1.52  sim_bw_subsumed:                        9
% 7.94/1.52  sim_fw_subsumption_res:                 8
% 7.94/1.52  sim_bw_subsumption_res:                 0
% 7.94/1.52  sim_tautology_del:                      22
% 7.94/1.52  sim_eq_tautology_del:                   49
% 7.94/1.52  sim_eq_res_simp:                        0
% 7.94/1.52  sim_fw_demodulated:                     34
% 7.94/1.52  sim_bw_demodulated:                     175
% 7.94/1.52  sim_light_normalised:                   163
% 7.94/1.52  sim_joinable_taut:                      0
% 7.94/1.52  sim_joinable_simp:                      0
% 7.94/1.52  sim_ac_normalised:                      0
% 7.94/1.52  sim_smt_subsumption:                    0
% 7.94/1.52  
%------------------------------------------------------------------------------
