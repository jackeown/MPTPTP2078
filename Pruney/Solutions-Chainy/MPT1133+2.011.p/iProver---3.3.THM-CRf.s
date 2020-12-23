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
% DateTime   : Thu Dec  3 12:11:49 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  355 (1181177 expanded)
%              Number of clauses        :  246 (272266 expanded)
%              Number of leaves         :   32 (349548 expanded)
%              Depth                    :   40
%              Number of atoms          : 1670 (13282849 expanded)
%              Number of equality atoms :  899 (1392592 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   30 (   4 average)
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

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f68,plain,(
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

fof(f67,plain,(
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

fof(f66,plain,(
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

fof(f65,plain,
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

fof(f69,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f64,f68,f67,f66,f65])).

fof(f110,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f69])).

fof(f114,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f69])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f69])).

fof(f109,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f69])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
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

fof(f57,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f56])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f113,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f69])).

fof(f112,plain,(
    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f69])).

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

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f51])).

fof(f102,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f124,plain,(
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
    inference(equality_resolution,[],[f102])).

fof(f104,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f105,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f106,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f107,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f116,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f115,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

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

fof(f46,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f99,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f97,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f123,plain,(
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
    inference(equality_resolution,[],[f103])).

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

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f121,plain,(
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
    inference(equality_resolution,[],[f101])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f122,plain,(
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
    inference(equality_resolution,[],[f100])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK1(X0,X1),X0,X1)
        & v1_funct_1(sK1(X0,X1))
        & v4_relat_1(sK1(X0,X1),X0)
        & v1_relat_1(sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK1(X0,X1),X0,X1)
      & v1_funct_1(sK1(X0,X1))
      & v4_relat_1(sK1(X0,X1),X0)
      & v1_relat_1(sK1(X0,X1))
      & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f59])).

fof(f94,plain,(
    ! [X0,X1] : v1_funct_2(sK1(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f60])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f54])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f118,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f90,plain,(
    ! [X0,X1] : m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3777,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_36,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3801,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3777,c_36])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_19,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_791,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_16,c_19])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_793,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_791,c_12,c_11])).

cnf(c_794,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_793])).

cnf(c_3767,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_4098,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_3767])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_54,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3776,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3800,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3776,c_36])).

cnf(c_4433,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4098,c_54,c_3800])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3796,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X0
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_3770,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_5461,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_3770])).

cnf(c_5826,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3796,c_5461])).

cnf(c_5931,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4433,c_5826])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_586,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X3 != X2
    | sK0(X3) != X0
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_587,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_3769,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK0(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_4930,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK0(sK5),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_3769])).

cnf(c_6015,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK0(sK5),k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5931,c_4930])).

cnf(c_6026,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5931,c_3800])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3780,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4350,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3780,c_3767])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_55,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4510,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4350,c_54,c_55])).

cnf(c_5460,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3780,c_3770])).

cnf(c_5831,plain,
    ( sK5 = k1_xboole_0
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3796,c_5460])).

cnf(c_5934,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4510,c_5831])).

cnf(c_33,plain,
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
    inference(cnf_transformation,[],[f124])).

cnf(c_3783,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6201,plain,
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
    inference(superposition,[status(thm)],[c_3780,c_3783])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_47,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_48,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_49,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_50,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_56,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,negated_conjecture,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3782,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3803,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3782,c_36])).

cnf(c_35,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3781,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3802,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3781,c_36])).

cnf(c_29,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3909,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3910,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3909])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3992,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3993,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3992])).

cnf(c_28,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4116,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_4117,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4116])).

cnf(c_32,plain,
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
    inference(cnf_transformation,[],[f123])).

cnf(c_4018,plain,
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
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_4254,plain,
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
    inference(instantiation,[status(thm)],[c_4018])).

cnf(c_4255,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4254])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f121])).

cnf(c_4017,plain,
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
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_4277,plain,
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
    inference(instantiation,[status(thm)],[c_4017])).

cnf(c_4278,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4277])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f122])).

cnf(c_4242,plain,
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
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_4664,plain,
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
    inference(instantiation,[status(thm)],[c_4242])).

cnf(c_4665,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_4664])).

cnf(c_6288,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6201,c_47,c_48,c_49,c_50,c_54,c_55,c_56,c_3801,c_3800,c_3803,c_3802,c_3910,c_3993,c_4117,c_4255,c_4278,c_4665])).

cnf(c_6289,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6288])).

cnf(c_6292,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6289,c_47,c_48,c_49,c_50,c_54,c_55,c_56,c_3801,c_3800,c_3802,c_3910,c_3993,c_4117,c_4255,c_4665])).

cnf(c_6552,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5934,c_6292])).

cnf(c_6025,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5931,c_3801])).

cnf(c_7046,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6552,c_6025])).

cnf(c_7047,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7046])).

cnf(c_7050,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5934,c_7047])).

cnf(c_7056,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6015,c_6026,c_7050])).

cnf(c_7083,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7056,c_3800])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3795,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4567,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3795,c_3767])).

cnf(c_10,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_122,plain,
    ( v1_funct_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_124,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_145,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8502,plain,
    ( v1_funct_2(k1_xboole_0,X0,X1) != iProver_top
    | k1_relat_1(k1_xboole_0) = X0
    | v1_xboole_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4567,c_124,c_145])).

cnf(c_8503,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_8502])).

cnf(c_3798,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3794,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3797,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5576,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3794,c_3797])).

cnf(c_8095,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3798,c_5576])).

cnf(c_8506,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8503,c_8095])).

cnf(c_8513,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7083,c_8506])).

cnf(c_8971,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8513,c_3797])).

cnf(c_20,plain,
    ( v1_funct_2(sK1(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_98,plain,
    ( v1_funct_2(sK1(X0,X1),X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_100,plain,
    ( v1_funct_2(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_137,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_138,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_139,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_141,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_24,plain,
    ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3790,plain,
    ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5459,plain,
    ( sK1(X0,X1) = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_3770])).

cnf(c_5468,plain,
    ( sK1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5459])).

cnf(c_3010,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_6466,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK1(X3,X4),X3,X4)
    | X1 != X3
    | X2 != X4
    | X0 != sK1(X3,X4) ),
    inference(instantiation,[status(thm)],[c_3010])).

cnf(c_6467,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != sK1(X1,X3)
    | v1_funct_2(X4,X0,X2) = iProver_top
    | v1_funct_2(sK1(X1,X3),X1,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6466])).

cnf(c_6469,plain,
    ( k1_xboole_0 != sK1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6467])).

cnf(c_3003,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8838,plain,
    ( X0 != X1
    | X0 = sK1(X2,X3)
    | sK1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_3003])).

cnf(c_8839,plain,
    ( sK1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8838])).

cnf(c_4621,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4433,c_3797])).

cnf(c_4718,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4621,c_4510])).

cnf(c_4622,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4510,c_3797])).

cnf(c_3779,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5304,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4622,c_3779])).

cnf(c_6297,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4621,c_6292])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_6298,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6297,c_3])).

cnf(c_134,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_136,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_3006,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_3019,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3006])).

cnf(c_3007,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4498,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(sK5,k1_zfmisc_1(X2))
    | k1_zfmisc_1(X2) != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_3007])).

cnf(c_5867,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4498])).

cnf(c_5868,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
    | sK5 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5867])).

cnf(c_5870,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK5 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5868])).

cnf(c_6695,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6298,c_136,c_137,c_138,c_3019,c_5870,c_6025,c_6552])).

cnf(c_6696,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6695])).

cnf(c_6701,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4621,c_6696])).

cnf(c_8256,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4718,c_5304,c_6701])).

cnf(c_8257,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_8256])).

cnf(c_8258,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
    | u1_struct_0(sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8257,c_7056,c_8095])).

cnf(c_9427,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6701,c_7056,c_8095])).

cnf(c_9430,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8258,c_9427])).

cnf(c_9497,plain,
    ( u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8971,c_100,c_137,c_138,c_141,c_145,c_5468,c_6469,c_8839,c_9430])).

cnf(c_7078,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7056,c_3802])).

cnf(c_9503,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9497,c_7078])).

cnf(c_7081,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7056,c_3779])).

cnf(c_9505,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9497,c_7081])).

cnf(c_7067,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7056,c_4622])).

cnf(c_10252,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7067,c_8095,c_9497])).

cnf(c_3786,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9516,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1) != iProver_top
    | v5_pre_topc(X0,sK2,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9497,c_3786])).

cnf(c_9538,plain,
    ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
    | v5_pre_topc(X0,sK2,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9516,c_9497])).

cnf(c_9539,plain,
    ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
    | v5_pre_topc(X0,sK2,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9538,c_4])).

cnf(c_10698,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
    | v5_pre_topc(X0,sK2,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9539,c_47,c_48])).

cnf(c_10699,plain,
    ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
    | v5_pre_topc(X0,sK2,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10698])).

cnf(c_10707,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10252,c_10699])).

cnf(c_10708,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10707,c_3])).

cnf(c_3924,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3925,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3924])).

cnf(c_4002,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_4003,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4002])).

cnf(c_4172,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_4173,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4172])).

cnf(c_10952,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10708,c_49,c_50,c_3925,c_4003,c_4173])).

cnf(c_10959,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9505,c_10952])).

cnf(c_3785,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9517,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1) = iProver_top
    | v5_pre_topc(X0,sK2,X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9497,c_3785])).

cnf(c_9536,plain,
    ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
    | v5_pre_topc(X0,sK2,X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9517,c_9497])).

cnf(c_9537,plain,
    ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
    | v5_pre_topc(X0,sK2,X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9536,c_4])).

cnf(c_10675,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
    | v5_pre_topc(X0,sK2,X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9537,c_47,c_48])).

cnf(c_10676,plain,
    ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
    | v5_pre_topc(X0,sK2,X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10675])).

cnf(c_10684,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10252,c_10676])).

cnf(c_10685,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10684,c_3])).

cnf(c_10937,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10685,c_49,c_50,c_3925,c_4003,c_4173])).

cnf(c_10944,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9505,c_10937])).

cnf(c_52,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3978,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_3003])).

cnf(c_3979,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3978])).

cnf(c_4053,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_3003])).

cnf(c_4291,plain,
    ( X0 = sK4
    | X0 != sK5
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_4053])).

cnf(c_4292,plain,
    ( sK4 != sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_4291])).

cnf(c_6461,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | X2 != u1_struct_0(sK3)
    | X1 != u1_struct_0(sK2)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_3010])).

cnf(c_6964,plain,
    ( v1_funct_2(X0,X1,u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | X1 != u1_struct_0(sK2)
    | X0 != sK4
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6461])).

cnf(c_6965,plain,
    ( X0 != u1_struct_0(sK2)
    | X1 != sK4
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v1_funct_2(X1,X0,u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6964])).

cnf(c_6967,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | k1_xboole_0 != u1_struct_0(sK2)
    | k1_xboole_0 != sK4
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6965])).

cnf(c_3002,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7294,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3002])).

cnf(c_7991,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_3003])).

cnf(c_7992,plain,
    ( u1_struct_0(sK2) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7991])).

cnf(c_7079,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7056,c_3803])).

cnf(c_9504,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9497,c_7079])).

cnf(c_3784,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9518,plain,
    ( v5_pre_topc(X0,sK2,X1) = iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9497,c_3784])).

cnf(c_9534,plain,
    ( v5_pre_topc(X0,sK2,X1) = iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9518,c_9497])).

cnf(c_9535,plain,
    ( v5_pre_topc(X0,sK2,X1) = iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9534,c_4])).

cnf(c_10166,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v5_pre_topc(X0,sK2,X1) = iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9535,c_47,c_48])).

cnf(c_10167,plain,
    ( v5_pre_topc(X0,sK2,X1) = iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10166])).

cnf(c_10269,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(X0,sK2,sK3) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10252,c_10167])).

cnf(c_10315,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,sK3) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10269])).

cnf(c_10940,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10937])).

cnf(c_11222,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10944,c_49,c_50,c_52,c_36,c_100,c_124,c_136,c_137,c_138,c_141,c_145,c_3979,c_4292,c_5468,c_6026,c_6469,c_6967,c_7050,c_7294,c_7992,c_8839,c_9430,c_9504,c_9505,c_10315,c_10940])).

cnf(c_10955,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10952])).

cnf(c_10276,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
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
    inference(superposition,[status(thm)],[c_10252,c_3783])).

cnf(c_10278,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
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
    inference(demodulation,[status(thm)],[c_10276,c_3])).

cnf(c_11108,plain,
    ( l1_pre_topc(X1) != iProver_top
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10278,c_49,c_50])).

cnf(c_11109,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,X1,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11108])).

cnf(c_11116,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,sK2,sK3) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9497,c_11109])).

cnf(c_11119,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,sK2,sK3) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11116,c_9497])).

cnf(c_11120,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,sK2,sK3) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11119,c_4])).

cnf(c_11134,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(X0,sK2,sK3) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11120,c_47,c_48])).

cnf(c_11137,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,sK3) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11134])).

cnf(c_11226,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11222,c_52,c_36,c_100,c_124,c_136,c_137,c_138,c_141,c_145,c_3979,c_4292,c_5468,c_6026,c_6469,c_6967,c_7050,c_7294,c_7992,c_8839,c_9430,c_9503,c_9505,c_10955,c_11137])).

cnf(c_11230,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10252,c_11226])).

cnf(c_11426,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10959,c_100,c_137,c_138,c_141,c_145,c_5468,c_6469,c_8839,c_11230])).

cnf(c_11428,plain,
    ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
    | v5_pre_topc(X0,sK2,X1) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11426,c_10699])).

cnf(c_11436,plain,
    ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
    | v5_pre_topc(X0,sK2,X1) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11428,c_4])).

cnf(c_11830,plain,
    ( v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,sK3) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9503,c_11436])).

cnf(c_11429,plain,
    ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
    | v5_pre_topc(X0,sK2,X1) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11426,c_10676])).

cnf(c_11435,plain,
    ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
    | v5_pre_topc(X0,sK2,X1) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11429,c_4])).

cnf(c_11697,plain,
    ( v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,sK3) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11435,c_9504])).

cnf(c_11432,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11426,c_9505])).

cnf(c_9519,plain,
    ( v5_pre_topc(X0,sK2,X1) != iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9497,c_3783])).

cnf(c_9532,plain,
    ( v5_pre_topc(X0,sK2,X1) != iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9519,c_9497])).

cnf(c_9533,plain,
    ( v5_pre_topc(X0,sK2,X1) != iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9532,c_4])).

cnf(c_10108,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v5_pre_topc(X0,sK2,X1) != iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9533,c_47,c_48])).

cnf(c_10109,plain,
    ( v5_pre_topc(X0,sK2,X1) != iProver_top
    | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10108])).

cnf(c_11526,plain,
    ( v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,sK3) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11432,c_10109])).

cnf(c_11525,plain,
    ( v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK2,sK3) = iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11432,c_10167])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11830,c_11697,c_11526,c_11525,c_11432,c_9430,c_8839,c_7992,c_7294,c_7056,c_6967,c_6469,c_5468,c_4292,c_4173,c_4003,c_3979,c_3925,c_145,c_141,c_138,c_137,c_136,c_124,c_100,c_36,c_52,c_50,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.68/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.00  
% 3.68/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/1.00  
% 3.68/1.00  ------  iProver source info
% 3.68/1.00  
% 3.68/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.68/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/1.00  git: non_committed_changes: false
% 3.68/1.00  git: last_make_outside_of_git: false
% 3.68/1.00  
% 3.68/1.00  ------ 
% 3.68/1.00  
% 3.68/1.00  ------ Input Options
% 3.68/1.00  
% 3.68/1.00  --out_options                           all
% 3.68/1.00  --tptp_safe_out                         true
% 3.68/1.00  --problem_path                          ""
% 3.68/1.00  --include_path                          ""
% 3.68/1.00  --clausifier                            res/vclausify_rel
% 3.68/1.00  --clausifier_options                    ""
% 3.68/1.00  --stdin                                 false
% 3.68/1.00  --stats_out                             all
% 3.68/1.00  
% 3.68/1.00  ------ General Options
% 3.68/1.00  
% 3.68/1.00  --fof                                   false
% 3.68/1.00  --time_out_real                         305.
% 3.68/1.00  --time_out_virtual                      -1.
% 3.68/1.00  --symbol_type_check                     false
% 3.68/1.00  --clausify_out                          false
% 3.68/1.00  --sig_cnt_out                           false
% 3.68/1.00  --trig_cnt_out                          false
% 3.68/1.00  --trig_cnt_out_tolerance                1.
% 3.68/1.00  --trig_cnt_out_sk_spl                   false
% 3.68/1.00  --abstr_cl_out                          false
% 3.68/1.00  
% 3.68/1.00  ------ Global Options
% 3.68/1.00  
% 3.68/1.00  --schedule                              default
% 3.68/1.00  --add_important_lit                     false
% 3.68/1.00  --prop_solver_per_cl                    1000
% 3.68/1.00  --min_unsat_core                        false
% 3.68/1.00  --soft_assumptions                      false
% 3.68/1.00  --soft_lemma_size                       3
% 3.68/1.00  --prop_impl_unit_size                   0
% 3.68/1.00  --prop_impl_unit                        []
% 3.68/1.00  --share_sel_clauses                     true
% 3.68/1.00  --reset_solvers                         false
% 3.68/1.00  --bc_imp_inh                            [conj_cone]
% 3.68/1.00  --conj_cone_tolerance                   3.
% 3.68/1.00  --extra_neg_conj                        none
% 3.68/1.00  --large_theory_mode                     true
% 3.68/1.00  --prolific_symb_bound                   200
% 3.68/1.00  --lt_threshold                          2000
% 3.68/1.00  --clause_weak_htbl                      true
% 3.68/1.00  --gc_record_bc_elim                     false
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing Options
% 3.68/1.00  
% 3.68/1.00  --preprocessing_flag                    true
% 3.68/1.00  --time_out_prep_mult                    0.1
% 3.68/1.00  --splitting_mode                        input
% 3.68/1.00  --splitting_grd                         true
% 3.68/1.00  --splitting_cvd                         false
% 3.68/1.00  --splitting_cvd_svl                     false
% 3.68/1.00  --splitting_nvd                         32
% 3.68/1.00  --sub_typing                            true
% 3.68/1.00  --prep_gs_sim                           true
% 3.68/1.00  --prep_unflatten                        true
% 3.68/1.00  --prep_res_sim                          true
% 3.68/1.00  --prep_upred                            true
% 3.68/1.00  --prep_sem_filter                       exhaustive
% 3.68/1.00  --prep_sem_filter_out                   false
% 3.68/1.00  --pred_elim                             true
% 3.68/1.00  --res_sim_input                         true
% 3.68/1.00  --eq_ax_congr_red                       true
% 3.68/1.00  --pure_diseq_elim                       true
% 3.68/1.00  --brand_transform                       false
% 3.68/1.00  --non_eq_to_eq                          false
% 3.68/1.00  --prep_def_merge                        true
% 3.68/1.00  --prep_def_merge_prop_impl              false
% 3.68/1.00  --prep_def_merge_mbd                    true
% 3.68/1.00  --prep_def_merge_tr_red                 false
% 3.68/1.00  --prep_def_merge_tr_cl                  false
% 3.68/1.00  --smt_preprocessing                     true
% 3.68/1.00  --smt_ac_axioms                         fast
% 3.68/1.00  --preprocessed_out                      false
% 3.68/1.00  --preprocessed_stats                    false
% 3.68/1.00  
% 3.68/1.00  ------ Abstraction refinement Options
% 3.68/1.00  
% 3.68/1.00  --abstr_ref                             []
% 3.68/1.00  --abstr_ref_prep                        false
% 3.68/1.00  --abstr_ref_until_sat                   false
% 3.68/1.00  --abstr_ref_sig_restrict                funpre
% 3.68/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/1.00  --abstr_ref_under                       []
% 3.68/1.00  
% 3.68/1.00  ------ SAT Options
% 3.68/1.00  
% 3.68/1.00  --sat_mode                              false
% 3.68/1.00  --sat_fm_restart_options                ""
% 3.68/1.00  --sat_gr_def                            false
% 3.68/1.00  --sat_epr_types                         true
% 3.68/1.00  --sat_non_cyclic_types                  false
% 3.68/1.00  --sat_finite_models                     false
% 3.68/1.00  --sat_fm_lemmas                         false
% 3.68/1.00  --sat_fm_prep                           false
% 3.68/1.00  --sat_fm_uc_incr                        true
% 3.68/1.00  --sat_out_model                         small
% 3.68/1.00  --sat_out_clauses                       false
% 3.68/1.00  
% 3.68/1.00  ------ QBF Options
% 3.68/1.00  
% 3.68/1.00  --qbf_mode                              false
% 3.68/1.00  --qbf_elim_univ                         false
% 3.68/1.00  --qbf_dom_inst                          none
% 3.68/1.00  --qbf_dom_pre_inst                      false
% 3.68/1.00  --qbf_sk_in                             false
% 3.68/1.00  --qbf_pred_elim                         true
% 3.68/1.00  --qbf_split                             512
% 3.68/1.00  
% 3.68/1.00  ------ BMC1 Options
% 3.68/1.00  
% 3.68/1.00  --bmc1_incremental                      false
% 3.68/1.00  --bmc1_axioms                           reachable_all
% 3.68/1.00  --bmc1_min_bound                        0
% 3.68/1.00  --bmc1_max_bound                        -1
% 3.68/1.00  --bmc1_max_bound_default                -1
% 3.68/1.00  --bmc1_symbol_reachability              true
% 3.68/1.00  --bmc1_property_lemmas                  false
% 3.68/1.00  --bmc1_k_induction                      false
% 3.68/1.00  --bmc1_non_equiv_states                 false
% 3.68/1.00  --bmc1_deadlock                         false
% 3.68/1.00  --bmc1_ucm                              false
% 3.68/1.00  --bmc1_add_unsat_core                   none
% 3.68/1.00  --bmc1_unsat_core_children              false
% 3.68/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/1.00  --bmc1_out_stat                         full
% 3.68/1.00  --bmc1_ground_init                      false
% 3.68/1.00  --bmc1_pre_inst_next_state              false
% 3.68/1.00  --bmc1_pre_inst_state                   false
% 3.68/1.00  --bmc1_pre_inst_reach_state             false
% 3.68/1.00  --bmc1_out_unsat_core                   false
% 3.68/1.00  --bmc1_aig_witness_out                  false
% 3.68/1.00  --bmc1_verbose                          false
% 3.68/1.00  --bmc1_dump_clauses_tptp                false
% 3.68/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.68/1.00  --bmc1_dump_file                        -
% 3.68/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.68/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.68/1.00  --bmc1_ucm_extend_mode                  1
% 3.68/1.00  --bmc1_ucm_init_mode                    2
% 3.68/1.00  --bmc1_ucm_cone_mode                    none
% 3.68/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.68/1.00  --bmc1_ucm_relax_model                  4
% 3.68/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.68/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/1.00  --bmc1_ucm_layered_model                none
% 3.68/1.00  --bmc1_ucm_max_lemma_size               10
% 3.68/1.00  
% 3.68/1.00  ------ AIG Options
% 3.68/1.00  
% 3.68/1.00  --aig_mode                              false
% 3.68/1.00  
% 3.68/1.00  ------ Instantiation Options
% 3.68/1.00  
% 3.68/1.00  --instantiation_flag                    true
% 3.68/1.00  --inst_sos_flag                         true
% 3.68/1.00  --inst_sos_phase                        true
% 3.68/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/1.00  --inst_lit_sel_side                     num_symb
% 3.68/1.00  --inst_solver_per_active                1400
% 3.68/1.00  --inst_solver_calls_frac                1.
% 3.68/1.00  --inst_passive_queue_type               priority_queues
% 3.68/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/1.00  --inst_passive_queues_freq              [25;2]
% 3.68/1.00  --inst_dismatching                      true
% 3.68/1.00  --inst_eager_unprocessed_to_passive     true
% 3.68/1.00  --inst_prop_sim_given                   true
% 3.68/1.00  --inst_prop_sim_new                     false
% 3.68/1.00  --inst_subs_new                         false
% 3.68/1.00  --inst_eq_res_simp                      false
% 3.68/1.00  --inst_subs_given                       false
% 3.68/1.00  --inst_orphan_elimination               true
% 3.68/1.00  --inst_learning_loop_flag               true
% 3.68/1.00  --inst_learning_start                   3000
% 3.68/1.00  --inst_learning_factor                  2
% 3.68/1.00  --inst_start_prop_sim_after_learn       3
% 3.68/1.00  --inst_sel_renew                        solver
% 3.68/1.00  --inst_lit_activity_flag                true
% 3.68/1.00  --inst_restr_to_given                   false
% 3.68/1.00  --inst_activity_threshold               500
% 3.68/1.00  --inst_out_proof                        true
% 3.68/1.00  
% 3.68/1.00  ------ Resolution Options
% 3.68/1.00  
% 3.68/1.00  --resolution_flag                       true
% 3.68/1.00  --res_lit_sel                           adaptive
% 3.68/1.00  --res_lit_sel_side                      none
% 3.68/1.00  --res_ordering                          kbo
% 3.68/1.00  --res_to_prop_solver                    active
% 3.68/1.00  --res_prop_simpl_new                    false
% 3.68/1.00  --res_prop_simpl_given                  true
% 3.68/1.00  --res_passive_queue_type                priority_queues
% 3.68/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/1.00  --res_passive_queues_freq               [15;5]
% 3.68/1.00  --res_forward_subs                      full
% 3.68/1.00  --res_backward_subs                     full
% 3.68/1.00  --res_forward_subs_resolution           true
% 3.68/1.00  --res_backward_subs_resolution          true
% 3.68/1.00  --res_orphan_elimination                true
% 3.68/1.00  --res_time_limit                        2.
% 3.68/1.00  --res_out_proof                         true
% 3.68/1.00  
% 3.68/1.00  ------ Superposition Options
% 3.68/1.00  
% 3.68/1.00  --superposition_flag                    true
% 3.68/1.00  --sup_passive_queue_type                priority_queues
% 3.68/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.68/1.00  --demod_completeness_check              fast
% 3.68/1.00  --demod_use_ground                      true
% 3.68/1.00  --sup_to_prop_solver                    passive
% 3.68/1.00  --sup_prop_simpl_new                    true
% 3.68/1.00  --sup_prop_simpl_given                  true
% 3.68/1.00  --sup_fun_splitting                     true
% 3.68/1.00  --sup_smt_interval                      50000
% 3.68/1.00  
% 3.68/1.00  ------ Superposition Simplification Setup
% 3.68/1.00  
% 3.68/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/1.00  --sup_immed_triv                        [TrivRules]
% 3.68/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/1.00  --sup_immed_bw_main                     []
% 3.68/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/1.00  --sup_input_bw                          []
% 3.68/1.00  
% 3.68/1.00  ------ Combination Options
% 3.68/1.00  
% 3.68/1.00  --comb_res_mult                         3
% 3.68/1.00  --comb_sup_mult                         2
% 3.68/1.00  --comb_inst_mult                        10
% 3.68/1.00  
% 3.68/1.00  ------ Debug Options
% 3.68/1.00  
% 3.68/1.00  --dbg_backtrace                         false
% 3.68/1.00  --dbg_dump_prop_clauses                 false
% 3.68/1.00  --dbg_dump_prop_clauses_file            -
% 3.68/1.00  --dbg_out_stat                          false
% 3.68/1.00  ------ Parsing...
% 3.68/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/1.00  ------ Proving...
% 3.68/1.00  ------ Problem Properties 
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  clauses                                 39
% 3.68/1.00  conjectures                             13
% 3.68/1.00  EPR                                     10
% 3.68/1.00  Horn                                    34
% 3.68/1.00  unary                                   18
% 3.68/1.01  binary                                  10
% 3.68/1.01  lits                                    108
% 3.68/1.01  lits eq                                 17
% 3.68/1.01  fd_pure                                 0
% 3.68/1.01  fd_pseudo                               0
% 3.68/1.01  fd_cond                                 6
% 3.68/1.01  fd_pseudo_cond                          2
% 3.68/1.01  AC symbols                              0
% 3.68/1.01  
% 3.68/1.01  ------ Schedule dynamic 5 is on 
% 3.68/1.01  
% 3.68/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/1.01  
% 3.68/1.01  
% 3.68/1.01  ------ 
% 3.68/1.01  Current options:
% 3.68/1.01  ------ 
% 3.68/1.01  
% 3.68/1.01  ------ Input Options
% 3.68/1.01  
% 3.68/1.01  --out_options                           all
% 3.68/1.01  --tptp_safe_out                         true
% 3.68/1.01  --problem_path                          ""
% 3.68/1.01  --include_path                          ""
% 3.68/1.01  --clausifier                            res/vclausify_rel
% 3.68/1.01  --clausifier_options                    ""
% 3.68/1.01  --stdin                                 false
% 3.68/1.01  --stats_out                             all
% 3.68/1.01  
% 3.68/1.01  ------ General Options
% 3.68/1.01  
% 3.68/1.01  --fof                                   false
% 3.68/1.01  --time_out_real                         305.
% 3.68/1.01  --time_out_virtual                      -1.
% 3.68/1.01  --symbol_type_check                     false
% 3.68/1.01  --clausify_out                          false
% 3.68/1.01  --sig_cnt_out                           false
% 3.68/1.01  --trig_cnt_out                          false
% 3.68/1.01  --trig_cnt_out_tolerance                1.
% 3.68/1.01  --trig_cnt_out_sk_spl                   false
% 3.68/1.01  --abstr_cl_out                          false
% 3.68/1.01  
% 3.68/1.01  ------ Global Options
% 3.68/1.01  
% 3.68/1.01  --schedule                              default
% 3.68/1.01  --add_important_lit                     false
% 3.68/1.01  --prop_solver_per_cl                    1000
% 3.68/1.01  --min_unsat_core                        false
% 3.68/1.01  --soft_assumptions                      false
% 3.68/1.01  --soft_lemma_size                       3
% 3.68/1.01  --prop_impl_unit_size                   0
% 3.68/1.01  --prop_impl_unit                        []
% 3.68/1.01  --share_sel_clauses                     true
% 3.68/1.01  --reset_solvers                         false
% 3.68/1.01  --bc_imp_inh                            [conj_cone]
% 3.68/1.01  --conj_cone_tolerance                   3.
% 3.68/1.01  --extra_neg_conj                        none
% 3.68/1.01  --large_theory_mode                     true
% 3.68/1.01  --prolific_symb_bound                   200
% 3.68/1.01  --lt_threshold                          2000
% 3.68/1.01  --clause_weak_htbl                      true
% 3.68/1.01  --gc_record_bc_elim                     false
% 3.68/1.01  
% 3.68/1.01  ------ Preprocessing Options
% 3.68/1.01  
% 3.68/1.01  --preprocessing_flag                    true
% 3.68/1.01  --time_out_prep_mult                    0.1
% 3.68/1.01  --splitting_mode                        input
% 3.68/1.01  --splitting_grd                         true
% 3.68/1.01  --splitting_cvd                         false
% 3.68/1.01  --splitting_cvd_svl                     false
% 3.68/1.01  --splitting_nvd                         32
% 3.68/1.01  --sub_typing                            true
% 3.68/1.01  --prep_gs_sim                           true
% 3.68/1.01  --prep_unflatten                        true
% 3.68/1.01  --prep_res_sim                          true
% 3.68/1.01  --prep_upred                            true
% 3.68/1.01  --prep_sem_filter                       exhaustive
% 3.68/1.01  --prep_sem_filter_out                   false
% 3.68/1.01  --pred_elim                             true
% 3.68/1.01  --res_sim_input                         true
% 3.68/1.01  --eq_ax_congr_red                       true
% 3.68/1.01  --pure_diseq_elim                       true
% 3.68/1.01  --brand_transform                       false
% 3.68/1.01  --non_eq_to_eq                          false
% 3.68/1.01  --prep_def_merge                        true
% 3.68/1.01  --prep_def_merge_prop_impl              false
% 3.68/1.01  --prep_def_merge_mbd                    true
% 3.68/1.01  --prep_def_merge_tr_red                 false
% 3.68/1.01  --prep_def_merge_tr_cl                  false
% 3.68/1.01  --smt_preprocessing                     true
% 3.68/1.01  --smt_ac_axioms                         fast
% 3.68/1.01  --preprocessed_out                      false
% 3.68/1.01  --preprocessed_stats                    false
% 3.68/1.01  
% 3.68/1.01  ------ Abstraction refinement Options
% 3.68/1.01  
% 3.68/1.01  --abstr_ref                             []
% 3.68/1.01  --abstr_ref_prep                        false
% 3.68/1.01  --abstr_ref_until_sat                   false
% 3.68/1.01  --abstr_ref_sig_restrict                funpre
% 3.68/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/1.01  --abstr_ref_under                       []
% 3.68/1.01  
% 3.68/1.01  ------ SAT Options
% 3.68/1.01  
% 3.68/1.01  --sat_mode                              false
% 3.68/1.01  --sat_fm_restart_options                ""
% 3.68/1.01  --sat_gr_def                            false
% 3.68/1.01  --sat_epr_types                         true
% 3.68/1.01  --sat_non_cyclic_types                  false
% 3.68/1.01  --sat_finite_models                     false
% 3.68/1.01  --sat_fm_lemmas                         false
% 3.68/1.01  --sat_fm_prep                           false
% 3.68/1.01  --sat_fm_uc_incr                        true
% 3.68/1.01  --sat_out_model                         small
% 3.68/1.01  --sat_out_clauses                       false
% 3.68/1.01  
% 3.68/1.01  ------ QBF Options
% 3.68/1.01  
% 3.68/1.01  --qbf_mode                              false
% 3.68/1.01  --qbf_elim_univ                         false
% 3.68/1.01  --qbf_dom_inst                          none
% 3.68/1.01  --qbf_dom_pre_inst                      false
% 3.68/1.01  --qbf_sk_in                             false
% 3.68/1.01  --qbf_pred_elim                         true
% 3.68/1.01  --qbf_split                             512
% 3.68/1.01  
% 3.68/1.01  ------ BMC1 Options
% 3.68/1.01  
% 3.68/1.01  --bmc1_incremental                      false
% 3.68/1.01  --bmc1_axioms                           reachable_all
% 3.68/1.01  --bmc1_min_bound                        0
% 3.68/1.01  --bmc1_max_bound                        -1
% 3.68/1.01  --bmc1_max_bound_default                -1
% 3.68/1.01  --bmc1_symbol_reachability              true
% 3.68/1.01  --bmc1_property_lemmas                  false
% 3.68/1.01  --bmc1_k_induction                      false
% 3.68/1.01  --bmc1_non_equiv_states                 false
% 3.68/1.01  --bmc1_deadlock                         false
% 3.68/1.01  --bmc1_ucm                              false
% 3.68/1.01  --bmc1_add_unsat_core                   none
% 3.68/1.01  --bmc1_unsat_core_children              false
% 3.68/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/1.01  --bmc1_out_stat                         full
% 3.68/1.01  --bmc1_ground_init                      false
% 3.68/1.01  --bmc1_pre_inst_next_state              false
% 3.68/1.01  --bmc1_pre_inst_state                   false
% 3.68/1.01  --bmc1_pre_inst_reach_state             false
% 3.68/1.01  --bmc1_out_unsat_core                   false
% 3.68/1.01  --bmc1_aig_witness_out                  false
% 3.68/1.01  --bmc1_verbose                          false
% 3.68/1.01  --bmc1_dump_clauses_tptp                false
% 3.68/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.68/1.01  --bmc1_dump_file                        -
% 3.68/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.68/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.68/1.01  --bmc1_ucm_extend_mode                  1
% 3.68/1.01  --bmc1_ucm_init_mode                    2
% 3.68/1.01  --bmc1_ucm_cone_mode                    none
% 3.68/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.68/1.01  --bmc1_ucm_relax_model                  4
% 3.68/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.68/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/1.01  --bmc1_ucm_layered_model                none
% 3.68/1.01  --bmc1_ucm_max_lemma_size               10
% 3.68/1.01  
% 3.68/1.01  ------ AIG Options
% 3.68/1.01  
% 3.68/1.01  --aig_mode                              false
% 3.68/1.01  
% 3.68/1.01  ------ Instantiation Options
% 3.68/1.01  
% 3.68/1.01  --instantiation_flag                    true
% 3.68/1.01  --inst_sos_flag                         true
% 3.68/1.01  --inst_sos_phase                        true
% 3.68/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/1.01  --inst_lit_sel_side                     none
% 3.68/1.01  --inst_solver_per_active                1400
% 3.68/1.01  --inst_solver_calls_frac                1.
% 3.68/1.01  --inst_passive_queue_type               priority_queues
% 3.68/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/1.01  --inst_passive_queues_freq              [25;2]
% 3.68/1.01  --inst_dismatching                      true
% 3.68/1.01  --inst_eager_unprocessed_to_passive     true
% 3.68/1.01  --inst_prop_sim_given                   true
% 3.68/1.01  --inst_prop_sim_new                     false
% 3.68/1.01  --inst_subs_new                         false
% 3.68/1.01  --inst_eq_res_simp                      false
% 3.68/1.01  --inst_subs_given                       false
% 3.68/1.01  --inst_orphan_elimination               true
% 3.68/1.01  --inst_learning_loop_flag               true
% 3.68/1.01  --inst_learning_start                   3000
% 3.68/1.01  --inst_learning_factor                  2
% 3.68/1.01  --inst_start_prop_sim_after_learn       3
% 3.68/1.01  --inst_sel_renew                        solver
% 3.68/1.01  --inst_lit_activity_flag                true
% 3.68/1.01  --inst_restr_to_given                   false
% 3.68/1.01  --inst_activity_threshold               500
% 3.68/1.01  --inst_out_proof                        true
% 3.68/1.01  
% 3.68/1.01  ------ Resolution Options
% 3.68/1.01  
% 3.68/1.01  --resolution_flag                       false
% 3.68/1.01  --res_lit_sel                           adaptive
% 3.68/1.01  --res_lit_sel_side                      none
% 3.68/1.01  --res_ordering                          kbo
% 3.68/1.01  --res_to_prop_solver                    active
% 3.68/1.01  --res_prop_simpl_new                    false
% 3.68/1.01  --res_prop_simpl_given                  true
% 3.68/1.01  --res_passive_queue_type                priority_queues
% 3.68/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/1.01  --res_passive_queues_freq               [15;5]
% 3.68/1.01  --res_forward_subs                      full
% 3.68/1.01  --res_backward_subs                     full
% 3.68/1.01  --res_forward_subs_resolution           true
% 3.68/1.01  --res_backward_subs_resolution          true
% 3.68/1.01  --res_orphan_elimination                true
% 3.68/1.01  --res_time_limit                        2.
% 3.68/1.01  --res_out_proof                         true
% 3.68/1.01  
% 3.68/1.01  ------ Superposition Options
% 3.68/1.01  
% 3.68/1.01  --superposition_flag                    true
% 3.68/1.01  --sup_passive_queue_type                priority_queues
% 3.68/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.68/1.01  --demod_completeness_check              fast
% 3.68/1.01  --demod_use_ground                      true
% 3.68/1.01  --sup_to_prop_solver                    passive
% 3.68/1.01  --sup_prop_simpl_new                    true
% 3.68/1.01  --sup_prop_simpl_given                  true
% 3.68/1.01  --sup_fun_splitting                     true
% 3.68/1.01  --sup_smt_interval                      50000
% 3.68/1.01  
% 3.68/1.01  ------ Superposition Simplification Setup
% 3.68/1.01  
% 3.68/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/1.01  --sup_immed_triv                        [TrivRules]
% 3.68/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/1.01  --sup_immed_bw_main                     []
% 3.68/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/1.01  --sup_input_bw                          []
% 3.68/1.01  
% 3.68/1.01  ------ Combination Options
% 3.68/1.01  
% 3.68/1.01  --comb_res_mult                         3
% 3.68/1.01  --comb_sup_mult                         2
% 3.68/1.01  --comb_inst_mult                        10
% 3.68/1.01  
% 3.68/1.01  ------ Debug Options
% 3.68/1.01  
% 3.68/1.01  --dbg_backtrace                         false
% 3.68/1.01  --dbg_dump_prop_clauses                 false
% 3.68/1.01  --dbg_dump_prop_clauses_file            -
% 3.68/1.01  --dbg_out_stat                          false
% 3.68/1.01  
% 3.68/1.01  
% 3.68/1.01  
% 3.68/1.01  
% 3.68/1.01  ------ Proving...
% 3.68/1.01  
% 3.68/1.01  
% 3.68/1.01  % SZS status Theorem for theBenchmark.p
% 3.68/1.01  
% 3.68/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/1.01  
% 3.68/1.01  fof(f22,conjecture,(
% 3.68/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f23,negated_conjecture,(
% 3.68/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.68/1.01    inference(negated_conjecture,[],[f22])).
% 3.68/1.01  
% 3.68/1.01  fof(f52,plain,(
% 3.68/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.68/1.01    inference(ennf_transformation,[],[f23])).
% 3.68/1.01  
% 3.68/1.01  fof(f53,plain,(
% 3.68/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.68/1.01    inference(flattening,[],[f52])).
% 3.68/1.01  
% 3.68/1.01  fof(f63,plain,(
% 3.68/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.68/1.01    inference(nnf_transformation,[],[f53])).
% 3.68/1.01  
% 3.68/1.01  fof(f64,plain,(
% 3.68/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.68/1.01    inference(flattening,[],[f63])).
% 3.68/1.01  
% 3.68/1.01  fof(f68,plain,(
% 3.68/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK5 = X2 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK5))) )),
% 3.68/1.01    introduced(choice_axiom,[])).
% 3.68/1.01  
% 3.68/1.01  fof(f67,plain,(
% 3.68/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK4,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK4,X0,X1)) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.68/1.01    introduced(choice_axiom,[])).
% 3.68/1.01  
% 3.68/1.01  fof(f66,plain,(
% 3.68/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(X2,X0,sK3)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(X2,X0,sK3)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))) )),
% 3.68/1.01    introduced(choice_axiom,[])).
% 3.68/1.01  
% 3.68/1.01  fof(f65,plain,(
% 3.68/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK2,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK2,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 3.68/1.01    introduced(choice_axiom,[])).
% 3.68/1.01  
% 3.68/1.01  fof(f69,plain,(
% 3.68/1.01    ((((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)) & sK4 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 3.68/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f64,f68,f67,f66,f65])).
% 3.68/1.01  
% 3.68/1.01  fof(f110,plain,(
% 3.68/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f114,plain,(
% 3.68/1.01    sK4 = sK5),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f13,axiom,(
% 3.68/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f38,plain,(
% 3.68/1.01    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.68/1.01    inference(ennf_transformation,[],[f13])).
% 3.68/1.01  
% 3.68/1.01  fof(f39,plain,(
% 3.68/1.01    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.68/1.01    inference(flattening,[],[f38])).
% 3.68/1.01  
% 3.68/1.01  fof(f87,plain,(
% 3.68/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f39])).
% 3.68/1.01  
% 3.68/1.01  fof(f14,axiom,(
% 3.68/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f40,plain,(
% 3.68/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.68/1.01    inference(ennf_transformation,[],[f14])).
% 3.68/1.01  
% 3.68/1.01  fof(f41,plain,(
% 3.68/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.68/1.01    inference(flattening,[],[f40])).
% 3.68/1.01  
% 3.68/1.01  fof(f58,plain,(
% 3.68/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.68/1.01    inference(nnf_transformation,[],[f41])).
% 3.68/1.01  
% 3.68/1.01  fof(f88,plain,(
% 3.68/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f58])).
% 3.68/1.01  
% 3.68/1.01  fof(f11,axiom,(
% 3.68/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f27,plain,(
% 3.68/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.68/1.01    inference(pure_predicate_removal,[],[f11])).
% 3.68/1.01  
% 3.68/1.01  fof(f36,plain,(
% 3.68/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/1.01    inference(ennf_transformation,[],[f27])).
% 3.68/1.01  
% 3.68/1.01  fof(f82,plain,(
% 3.68/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/1.01    inference(cnf_transformation,[],[f36])).
% 3.68/1.01  
% 3.68/1.01  fof(f10,axiom,(
% 3.68/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f35,plain,(
% 3.68/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/1.01    inference(ennf_transformation,[],[f10])).
% 3.68/1.01  
% 3.68/1.01  fof(f81,plain,(
% 3.68/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/1.01    inference(cnf_transformation,[],[f35])).
% 3.68/1.01  
% 3.68/1.01  fof(f111,plain,(
% 3.68/1.01    v1_funct_1(sK5)),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f109,plain,(
% 3.68/1.01    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f3,axiom,(
% 3.68/1.01    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f29,plain,(
% 3.68/1.01    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.68/1.01    inference(ennf_transformation,[],[f3])).
% 3.68/1.01  
% 3.68/1.01  fof(f72,plain,(
% 3.68/1.01    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f29])).
% 3.68/1.01  
% 3.68/1.01  fof(f7,axiom,(
% 3.68/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f32,plain,(
% 3.68/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.68/1.01    inference(ennf_transformation,[],[f7])).
% 3.68/1.01  
% 3.68/1.01  fof(f78,plain,(
% 3.68/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f32])).
% 3.68/1.01  
% 3.68/1.01  fof(f12,axiom,(
% 3.68/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f37,plain,(
% 3.68/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.68/1.01    inference(ennf_transformation,[],[f12])).
% 3.68/1.01  
% 3.68/1.01  fof(f56,plain,(
% 3.68/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.68/1.01    introduced(choice_axiom,[])).
% 3.68/1.01  
% 3.68/1.01  fof(f57,plain,(
% 3.68/1.01    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.68/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f56])).
% 3.68/1.01  
% 3.68/1.01  fof(f83,plain,(
% 3.68/1.01    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.68/1.01    inference(cnf_transformation,[],[f57])).
% 3.68/1.01  
% 3.68/1.01  fof(f6,axiom,(
% 3.68/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f30,plain,(
% 3.68/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.68/1.01    inference(ennf_transformation,[],[f6])).
% 3.68/1.01  
% 3.68/1.01  fof(f31,plain,(
% 3.68/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.68/1.01    inference(flattening,[],[f30])).
% 3.68/1.01  
% 3.68/1.01  fof(f77,plain,(
% 3.68/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f31])).
% 3.68/1.01  
% 3.68/1.01  fof(f113,plain,(
% 3.68/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f112,plain,(
% 3.68/1.01    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f21,axiom,(
% 3.68/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f50,plain,(
% 3.68/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.68/1.01    inference(ennf_transformation,[],[f21])).
% 3.68/1.01  
% 3.68/1.01  fof(f51,plain,(
% 3.68/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/1.01    inference(flattening,[],[f50])).
% 3.68/1.01  
% 3.68/1.01  fof(f62,plain,(
% 3.68/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/1.01    inference(nnf_transformation,[],[f51])).
% 3.68/1.01  
% 3.68/1.01  fof(f102,plain,(
% 3.68/1.01    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f62])).
% 3.68/1.01  
% 3.68/1.01  fof(f124,plain,(
% 3.68/1.01    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/1.01    inference(equality_resolution,[],[f102])).
% 3.68/1.01  
% 3.68/1.01  fof(f104,plain,(
% 3.68/1.01    v2_pre_topc(sK2)),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f105,plain,(
% 3.68/1.01    l1_pre_topc(sK2)),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f106,plain,(
% 3.68/1.01    v2_pre_topc(sK3)),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f107,plain,(
% 3.68/1.01    l1_pre_topc(sK3)),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f116,plain,(
% 3.68/1.01    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f115,plain,(
% 3.68/1.01    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)),
% 3.68/1.01    inference(cnf_transformation,[],[f69])).
% 3.68/1.01  
% 3.68/1.01  fof(f19,axiom,(
% 3.68/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f24,plain,(
% 3.68/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 3.68/1.01    inference(pure_predicate_removal,[],[f19])).
% 3.68/1.01  
% 3.68/1.01  fof(f46,plain,(
% 3.68/1.01    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.68/1.01    inference(ennf_transformation,[],[f24])).
% 3.68/1.01  
% 3.68/1.01  fof(f47,plain,(
% 3.68/1.01    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/1.01    inference(flattening,[],[f46])).
% 3.68/1.01  
% 3.68/1.01  fof(f99,plain,(
% 3.68/1.01    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f47])).
% 3.68/1.01  
% 3.68/1.01  fof(f17,axiom,(
% 3.68/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f25,plain,(
% 3.68/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 3.68/1.01    inference(pure_predicate_removal,[],[f17])).
% 3.68/1.01  
% 3.68/1.01  fof(f44,plain,(
% 3.68/1.01    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.68/1.01    inference(ennf_transformation,[],[f25])).
% 3.68/1.01  
% 3.68/1.01  fof(f97,plain,(
% 3.68/1.01    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.68/1.01    inference(cnf_transformation,[],[f44])).
% 3.68/1.01  
% 3.68/1.01  fof(f18,axiom,(
% 3.68/1.01    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f45,plain,(
% 3.68/1.01    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.68/1.01    inference(ennf_transformation,[],[f18])).
% 3.68/1.01  
% 3.68/1.01  fof(f98,plain,(
% 3.68/1.01    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f45])).
% 3.68/1.01  
% 3.68/1.01  fof(f103,plain,(
% 3.68/1.01    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f62])).
% 3.68/1.01  
% 3.68/1.01  fof(f123,plain,(
% 3.68/1.01    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/1.01    inference(equality_resolution,[],[f103])).
% 3.68/1.01  
% 3.68/1.01  fof(f20,axiom,(
% 3.68/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f48,plain,(
% 3.68/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.68/1.01    inference(ennf_transformation,[],[f20])).
% 3.68/1.01  
% 3.68/1.01  fof(f49,plain,(
% 3.68/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/1.01    inference(flattening,[],[f48])).
% 3.68/1.01  
% 3.68/1.01  fof(f61,plain,(
% 3.68/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/1.01    inference(nnf_transformation,[],[f49])).
% 3.68/1.01  
% 3.68/1.01  fof(f101,plain,(
% 3.68/1.01    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f61])).
% 3.68/1.01  
% 3.68/1.01  fof(f121,plain,(
% 3.68/1.01    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/1.01    inference(equality_resolution,[],[f101])).
% 3.68/1.01  
% 3.68/1.01  fof(f100,plain,(
% 3.68/1.01    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f61])).
% 3.68/1.01  
% 3.68/1.01  fof(f122,plain,(
% 3.68/1.01    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.68/1.01    inference(equality_resolution,[],[f100])).
% 3.68/1.01  
% 3.68/1.01  fof(f5,axiom,(
% 3.68/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f76,plain,(
% 3.68/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.68/1.01    inference(cnf_transformation,[],[f5])).
% 3.68/1.01  
% 3.68/1.01  fof(f9,axiom,(
% 3.68/1.01    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f34,plain,(
% 3.68/1.01    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.68/1.01    inference(ennf_transformation,[],[f9])).
% 3.68/1.01  
% 3.68/1.01  fof(f80,plain,(
% 3.68/1.01    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f34])).
% 3.68/1.01  
% 3.68/1.01  fof(f1,axiom,(
% 3.68/1.01    v1_xboole_0(k1_xboole_0)),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f70,plain,(
% 3.68/1.01    v1_xboole_0(k1_xboole_0)),
% 3.68/1.01    inference(cnf_transformation,[],[f1])).
% 3.68/1.01  
% 3.68/1.01  fof(f8,axiom,(
% 3.68/1.01    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f33,plain,(
% 3.68/1.01    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.68/1.01    inference(ennf_transformation,[],[f8])).
% 3.68/1.01  
% 3.68/1.01  fof(f79,plain,(
% 3.68/1.01    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f33])).
% 3.68/1.01  
% 3.68/1.01  fof(f2,axiom,(
% 3.68/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f28,plain,(
% 3.68/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.68/1.01    inference(ennf_transformation,[],[f2])).
% 3.68/1.01  
% 3.68/1.01  fof(f71,plain,(
% 3.68/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f28])).
% 3.68/1.01  
% 3.68/1.01  fof(f15,axiom,(
% 3.68/1.01    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f26,plain,(
% 3.68/1.01    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/1.01    inference(pure_predicate_removal,[],[f15])).
% 3.68/1.01  
% 3.68/1.01  fof(f59,plain,(
% 3.68/1.01    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK1(X0,X1),X0,X1) & v1_funct_1(sK1(X0,X1)) & v4_relat_1(sK1(X0,X1),X0) & v1_relat_1(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.68/1.01    introduced(choice_axiom,[])).
% 3.68/1.01  
% 3.68/1.01  fof(f60,plain,(
% 3.68/1.01    ! [X0,X1] : (v1_funct_2(sK1(X0,X1),X0,X1) & v1_funct_1(sK1(X0,X1)) & v4_relat_1(sK1(X0,X1),X0) & v1_relat_1(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f59])).
% 3.68/1.01  
% 3.68/1.01  fof(f94,plain,(
% 3.68/1.01    ( ! [X0,X1] : (v1_funct_2(sK1(X0,X1),X0,X1)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f60])).
% 3.68/1.01  
% 3.68/1.01  fof(f4,axiom,(
% 3.68/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.68/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/1.01  
% 3.68/1.01  fof(f54,plain,(
% 3.68/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.68/1.01    inference(nnf_transformation,[],[f4])).
% 3.68/1.01  
% 3.68/1.01  fof(f55,plain,(
% 3.68/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.68/1.01    inference(flattening,[],[f54])).
% 3.68/1.01  
% 3.68/1.01  fof(f73,plain,(
% 3.68/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.68/1.01    inference(cnf_transformation,[],[f55])).
% 3.68/1.01  
% 3.68/1.01  fof(f74,plain,(
% 3.68/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.68/1.01    inference(cnf_transformation,[],[f55])).
% 3.68/1.01  
% 3.68/1.01  fof(f118,plain,(
% 3.68/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.68/1.01    inference(equality_resolution,[],[f74])).
% 3.68/1.01  
% 3.68/1.01  fof(f90,plain,(
% 3.68/1.01    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/1.01    inference(cnf_transformation,[],[f60])).
% 3.68/1.01  
% 3.68/1.01  fof(f75,plain,(
% 3.68/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.68/1.01    inference(cnf_transformation,[],[f55])).
% 3.68/1.01  
% 3.68/1.01  fof(f117,plain,(
% 3.68/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.68/1.01    inference(equality_resolution,[],[f75])).
% 3.68/1.01  
% 3.68/1.01  cnf(c_40,negated_conjecture,
% 3.68/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.68/1.01      inference(cnf_transformation,[],[f110]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3777,plain,
% 3.68/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_36,negated_conjecture,
% 3.68/1.01      ( sK4 = sK5 ),
% 3.68/1.01      inference(cnf_transformation,[],[f114]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3801,plain,
% 3.68/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_3777,c_36]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_16,plain,
% 3.68/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/1.01      | v1_partfun1(X0,X1)
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/1.01      | ~ v1_funct_1(X0)
% 3.68/1.01      | v1_xboole_0(X2) ),
% 3.68/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_19,plain,
% 3.68/1.01      ( ~ v1_partfun1(X0,X1)
% 3.68/1.01      | ~ v4_relat_1(X0,X1)
% 3.68/1.01      | ~ v1_relat_1(X0)
% 3.68/1.01      | k1_relat_1(X0) = X1 ),
% 3.68/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_791,plain,
% 3.68/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/1.01      | ~ v4_relat_1(X0,X1)
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/1.01      | ~ v1_relat_1(X0)
% 3.68/1.01      | ~ v1_funct_1(X0)
% 3.68/1.01      | v1_xboole_0(X2)
% 3.68/1.01      | k1_relat_1(X0) = X1 ),
% 3.68/1.01      inference(resolution,[status(thm)],[c_16,c_19]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_12,plain,
% 3.68/1.01      ( v4_relat_1(X0,X1)
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.68/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11,plain,
% 3.68/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/1.01      | v1_relat_1(X0) ),
% 3.68/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_793,plain,
% 3.68/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/1.01      | ~ v1_funct_2(X0,X1,X2)
% 3.68/1.01      | ~ v1_funct_1(X0)
% 3.68/1.01      | v1_xboole_0(X2)
% 3.68/1.01      | k1_relat_1(X0) = X1 ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_791,c_12,c_11]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_794,plain,
% 3.68/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/1.01      | ~ v1_funct_1(X0)
% 3.68/1.01      | v1_xboole_0(X2)
% 3.68/1.01      | k1_relat_1(X0) = X1 ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_793]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3767,plain,
% 3.68/1.01      ( k1_relat_1(X0) = X1
% 3.68/1.01      | v1_funct_2(X0,X1,X2) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top
% 3.68/1.01      | v1_xboole_0(X2) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4098,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | v1_funct_1(sK5) != iProver_top
% 3.68/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3801,c_3767]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_39,negated_conjecture,
% 3.68/1.01      ( v1_funct_1(sK5) ),
% 3.68/1.01      inference(cnf_transformation,[],[f111]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_54,plain,
% 3.68/1.01      ( v1_funct_1(sK5) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_41,negated_conjecture,
% 3.68/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.68/1.01      inference(cnf_transformation,[],[f109]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3776,plain,
% 3.68/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3800,plain,
% 3.68/1.01      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_3776,c_36]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4433,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.68/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_4098,c_54,c_3800]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_2,plain,
% 3.68/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.68/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3796,plain,
% 3.68/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.68/1.01      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8,plain,
% 3.68/1.01      ( ~ r2_hidden(X0,X1)
% 3.68/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.68/1.01      | ~ v1_xboole_0(X2) ),
% 3.68/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_15,plain,
% 3.68/1.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.68/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_573,plain,
% 3.68/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/1.01      | ~ v1_xboole_0(X1)
% 3.68/1.01      | X2 != X0
% 3.68/1.01      | sK0(X2) != X3
% 3.68/1.01      | k1_xboole_0 = X2 ),
% 3.68/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_574,plain,
% 3.68/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/1.01      | ~ v1_xboole_0(X1)
% 3.68/1.01      | k1_xboole_0 = X0 ),
% 3.68/1.01      inference(unflattening,[status(thm)],[c_573]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3770,plain,
% 3.68/1.01      ( k1_xboole_0 = X0
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.68/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5461,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3801,c_3770]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5826,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3796,c_5461]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5931,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_relat_1(sK5) | sK5 = k1_xboole_0 ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_4433,c_5826]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7,plain,
% 3.68/1.01      ( ~ r2_hidden(X0,X1)
% 3.68/1.01      | m1_subset_1(X0,X2)
% 3.68/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.68/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_586,plain,
% 3.68/1.01      ( m1_subset_1(X0,X1)
% 3.68/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.68/1.01      | X3 != X2
% 3.68/1.01      | sK0(X3) != X0
% 3.68/1.01      | k1_xboole_0 = X3 ),
% 3.68/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_587,plain,
% 3.68/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/1.01      | m1_subset_1(sK0(X0),X1)
% 3.68/1.01      | k1_xboole_0 = X0 ),
% 3.68/1.01      inference(unflattening,[status(thm)],[c_586]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3769,plain,
% 3.68/1.01      ( k1_xboole_0 = X0
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(sK0(X0),X1) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4930,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | m1_subset_1(sK0(sK5),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3801,c_3769]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6015,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | m1_subset_1(sK0(sK5),k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3))) = iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_5931,c_4930]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6026,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_5931,c_3800]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_37,negated_conjecture,
% 3.68/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
% 3.68/1.01      inference(cnf_transformation,[],[f113]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3780,plain,
% 3.68/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4350,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_1(sK5) != iProver_top
% 3.68/1.01      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3780,c_3767]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_38,negated_conjecture,
% 3.68/1.01      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
% 3.68/1.01      inference(cnf_transformation,[],[f112]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_55,plain,
% 3.68/1.01      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4510,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 3.68/1.01      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_4350,c_54,c_55]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5460,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3780,c_3770]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5831,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3796,c_5460]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5934,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 3.68/1.01      | sK5 = k1_xboole_0 ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_4510,c_5831]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_33,plain,
% 3.68/1.01      ( ~ v5_pre_topc(X0,X1,X2)
% 3.68/1.01      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.68/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.68/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.68/1.01      | ~ v2_pre_topc(X1)
% 3.68/1.01      | ~ v2_pre_topc(X2)
% 3.68/1.01      | ~ l1_pre_topc(X1)
% 3.68/1.01      | ~ l1_pre_topc(X2)
% 3.68/1.01      | ~ v1_funct_1(X0) ),
% 3.68/1.01      inference(cnf_transformation,[],[f124]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3783,plain,
% 3.68/1.01      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(X2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6201,plain,
% 3.68/1.01      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.01      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3780,c_3783]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_46,negated_conjecture,
% 3.68/1.01      ( v2_pre_topc(sK2) ),
% 3.68/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_47,plain,
% 3.68/1.01      ( v2_pre_topc(sK2) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_45,negated_conjecture,
% 3.68/1.01      ( l1_pre_topc(sK2) ),
% 3.68/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_48,plain,
% 3.68/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_44,negated_conjecture,
% 3.68/1.01      ( v2_pre_topc(sK3) ),
% 3.68/1.01      inference(cnf_transformation,[],[f106]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_49,plain,
% 3.68/1.01      ( v2_pre_topc(sK3) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_43,negated_conjecture,
% 3.68/1.01      ( l1_pre_topc(sK3) ),
% 3.68/1.01      inference(cnf_transformation,[],[f107]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_50,plain,
% 3.68/1.01      ( l1_pre_topc(sK3) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_56,plain,
% 3.68/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_34,negated_conjecture,
% 3.68/1.01      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 3.68/1.01      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 3.68/1.01      inference(cnf_transformation,[],[f116]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3782,plain,
% 3.68/1.01      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 3.68/1.01      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3803,plain,
% 3.68/1.01      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_3782,c_36]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_35,negated_conjecture,
% 3.68/1.01      ( v5_pre_topc(sK4,sK2,sK3)
% 3.68/1.01      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 3.68/1.01      inference(cnf_transformation,[],[f115]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3781,plain,
% 3.68/1.01      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 3.68/1.01      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3802,plain,
% 3.68/1.01      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_3781,c_36]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_29,plain,
% 3.68/1.01      ( ~ v2_pre_topc(X0)
% 3.68/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.68/1.01      | ~ l1_pre_topc(X0) ),
% 3.68/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3909,plain,
% 3.68/1.01      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.68/1.01      | ~ v2_pre_topc(sK2)
% 3.68/1.01      | ~ l1_pre_topc(sK2) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3910,plain,
% 3.68/1.01      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_3909]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_27,plain,
% 3.68/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.68/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3992,plain,
% 3.68/1.01      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_27]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3993,plain,
% 3.68/1.01      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_3992]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_28,plain,
% 3.68/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.68/1.01      | ~ l1_pre_topc(X0) ),
% 3.68/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4116,plain,
% 3.68/1.01      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.68/1.01      | ~ l1_pre_topc(sK2) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4117,plain,
% 3.68/1.01      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_4116]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_32,plain,
% 3.68/1.01      ( v5_pre_topc(X0,X1,X2)
% 3.68/1.01      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 3.68/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.68/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 3.68/1.01      | ~ v2_pre_topc(X1)
% 3.68/1.01      | ~ v2_pre_topc(X2)
% 3.68/1.01      | ~ l1_pre_topc(X1)
% 3.68/1.01      | ~ l1_pre_topc(X2)
% 3.68/1.01      | ~ v1_funct_1(X0) ),
% 3.68/1.01      inference(cnf_transformation,[],[f123]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4018,plain,
% 3.68/1.01      ( ~ v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/1.01      | v5_pre_topc(sK5,X0,sK3)
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.68/1.01      | ~ v2_pre_topc(X0)
% 3.68/1.01      | ~ v2_pre_topc(sK3)
% 3.68/1.01      | ~ l1_pre_topc(X0)
% 3.68/1.01      | ~ l1_pre_topc(sK3)
% 3.68/1.01      | ~ v1_funct_1(sK5) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_32]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4254,plain,
% 3.68/1.01      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/1.01      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 3.68/1.01      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.68/1.01      | ~ v2_pre_topc(sK3)
% 3.68/1.01      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.68/1.01      | ~ l1_pre_topc(sK3)
% 3.68/1.01      | ~ v1_funct_1(sK5) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_4018]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4255,plain,
% 3.68/1.01      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.01      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_4254]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_30,plain,
% 3.68/1.01      ( v5_pre_topc(X0,X1,X2)
% 3.68/1.01      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.68/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.68/1.01      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.68/1.01      | ~ v2_pre_topc(X1)
% 3.68/1.01      | ~ v2_pre_topc(X2)
% 3.68/1.01      | ~ l1_pre_topc(X1)
% 3.68/1.01      | ~ l1_pre_topc(X2)
% 3.68/1.01      | ~ v1_funct_1(X0) ),
% 3.68/1.01      inference(cnf_transformation,[],[f121]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4017,plain,
% 3.68/1.01      ( v5_pre_topc(sK5,X0,sK3)
% 3.68/1.01      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
% 3.68/1.01      | ~ v2_pre_topc(X0)
% 3.68/1.01      | ~ v2_pre_topc(sK3)
% 3.68/1.01      | ~ l1_pre_topc(X0)
% 3.68/1.01      | ~ l1_pre_topc(sK3)
% 3.68/1.01      | ~ v1_funct_1(sK5) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4277,plain,
% 3.68/1.01      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.68/1.01      | v5_pre_topc(sK5,sK2,sK3)
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.68/1.01      | ~ v2_pre_topc(sK3)
% 3.68/1.01      | ~ v2_pre_topc(sK2)
% 3.68/1.01      | ~ l1_pre_topc(sK3)
% 3.68/1.01      | ~ l1_pre_topc(sK2)
% 3.68/1.01      | ~ v1_funct_1(sK5) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_4017]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4278,plain,
% 3.68/1.01      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 3.68/1.01      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_4277]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_31,plain,
% 3.68/1.01      ( ~ v5_pre_topc(X0,X1,X2)
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 3.68/1.01      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.68/1.01      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.68/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 3.68/1.01      | ~ v2_pre_topc(X1)
% 3.68/1.01      | ~ v2_pre_topc(X2)
% 3.68/1.01      | ~ l1_pre_topc(X1)
% 3.68/1.01      | ~ l1_pre_topc(X2)
% 3.68/1.01      | ~ v1_funct_1(X0) ),
% 3.68/1.01      inference(cnf_transformation,[],[f122]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4242,plain,
% 3.68/1.01      ( ~ v5_pre_topc(sK5,X0,sK3)
% 3.68/1.01      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
% 3.68/1.01      | ~ v2_pre_topc(X0)
% 3.68/1.01      | ~ v2_pre_topc(sK3)
% 3.68/1.01      | ~ l1_pre_topc(X0)
% 3.68/1.01      | ~ l1_pre_topc(sK3)
% 3.68/1.01      | ~ v1_funct_1(sK5) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_31]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4664,plain,
% 3.68/1.01      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 3.68/1.01      | ~ v5_pre_topc(sK5,sK2,sK3)
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 3.68/1.01      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 3.68/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.68/1.01      | ~ v2_pre_topc(sK3)
% 3.68/1.01      | ~ v2_pre_topc(sK2)
% 3.68/1.01      | ~ l1_pre_topc(sK3)
% 3.68/1.01      | ~ l1_pre_topc(sK2)
% 3.68/1.01      | ~ v1_funct_1(sK5) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_4242]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4665,plain,
% 3.68/1.01      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 3.68/1.01      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(sK5) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_4664]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6288,plain,
% 3.68/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_6201,c_47,c_48,c_49,c_50,c_54,c_55,c_56,c_3801,c_3800,
% 3.68/1.01                 c_3803,c_3802,c_3910,c_3993,c_4117,c_4255,c_4278,c_4665]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6289,plain,
% 3.68/1.01      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_6288]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6292,plain,
% 3.68/1.01      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_6289,c_47,c_48,c_49,c_50,c_54,c_55,c_56,c_3801,c_3800,
% 3.68/1.01                 c_3802,c_3910,c_3993,c_4117,c_4255,c_4665]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6552,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_5934,c_6292]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6025,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_5931,c_3801]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7046,plain,
% 3.68/1.01      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | sK5 = k1_xboole_0 ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_6552,c_6025]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7047,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_7046]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7050,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0
% 3.68/1.01      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(sK3)) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_5934,c_7047]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7056,plain,
% 3.68/1.01      ( sK5 = k1_xboole_0 ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_6015,c_6026,c_7050]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7083,plain,
% 3.68/1.01      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_7056,c_3800]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6,plain,
% 3.68/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.68/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3795,plain,
% 3.68/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4567,plain,
% 3.68/1.01      ( k1_relat_1(k1_xboole_0) = X0
% 3.68/1.01      | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.68/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3795,c_3767]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10,plain,
% 3.68/1.01      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.68/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_122,plain,
% 3.68/1.01      ( v1_funct_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_124,plain,
% 3.68/1.01      ( v1_funct_1(k1_xboole_0) = iProver_top
% 3.68/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_122]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_0,plain,
% 3.68/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.68/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_145,plain,
% 3.68/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8502,plain,
% 3.68/1.01      ( v1_funct_2(k1_xboole_0,X0,X1) != iProver_top
% 3.68/1.01      | k1_relat_1(k1_xboole_0) = X0
% 3.68/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_4567,c_124,c_145]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8503,plain,
% 3.68/1.01      ( k1_relat_1(k1_xboole_0) = X0
% 3.68/1.01      | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top
% 3.68/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_8502]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3798,plain,
% 3.68/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9,plain,
% 3.68/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 3.68/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3794,plain,
% 3.68/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.68/1.01      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_1,plain,
% 3.68/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.68/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3797,plain,
% 3.68/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5576,plain,
% 3.68/1.01      ( k1_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3794,c_3797]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8095,plain,
% 3.68/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3798,c_5576]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8506,plain,
% 3.68/1.01      ( k1_xboole_0 = X0
% 3.68/1.01      | v1_funct_2(k1_xboole_0,X0,X1) != iProver_top
% 3.68/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_8503,c_8095]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8513,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_xboole_0
% 3.68/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_7083,c_8506]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8971,plain,
% 3.68/1.01      ( u1_struct_0(sK3) = k1_xboole_0 | u1_struct_0(sK2) = k1_xboole_0 ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_8513,c_3797]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_20,plain,
% 3.68/1.01      ( v1_funct_2(sK1(X0,X1),X0,X1) ),
% 3.68/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_98,plain,
% 3.68/1.01      ( v1_funct_2(sK1(X0,X1),X0,X1) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_100,plain,
% 3.68/1.01      ( v1_funct_2(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_98]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5,plain,
% 3.68/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.68/1.01      | k1_xboole_0 = X0
% 3.68/1.01      | k1_xboole_0 = X1 ),
% 3.68/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_137,plain,
% 3.68/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.68/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4,plain,
% 3.68/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.68/1.01      inference(cnf_transformation,[],[f118]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_138,plain,
% 3.68/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_139,plain,
% 3.68/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.68/1.01      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_141,plain,
% 3.68/1.01      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.68/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_139]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_24,plain,
% 3.68/1.01      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.68/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3790,plain,
% 3.68/1.01      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5459,plain,
% 3.68/1.01      ( sK1(X0,X1) = k1_xboole_0
% 3.68/1.01      | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_3790,c_3770]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5468,plain,
% 3.68/1.01      ( sK1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 3.68/1.01      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_5459]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3010,plain,
% 3.68/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/1.01      | v1_funct_2(X3,X4,X5)
% 3.68/1.01      | X3 != X0
% 3.68/1.01      | X4 != X1
% 3.68/1.01      | X5 != X2 ),
% 3.68/1.01      theory(equality) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6466,plain,
% 3.68/1.01      ( v1_funct_2(X0,X1,X2)
% 3.68/1.01      | ~ v1_funct_2(sK1(X3,X4),X3,X4)
% 3.68/1.01      | X1 != X3
% 3.68/1.01      | X2 != X4
% 3.68/1.01      | X0 != sK1(X3,X4) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_3010]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6467,plain,
% 3.68/1.01      ( X0 != X1
% 3.68/1.01      | X2 != X3
% 3.68/1.01      | X4 != sK1(X1,X3)
% 3.68/1.01      | v1_funct_2(X4,X0,X2) = iProver_top
% 3.68/1.01      | v1_funct_2(sK1(X1,X3),X1,X3) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_6466]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6469,plain,
% 3.68/1.01      ( k1_xboole_0 != sK1(k1_xboole_0,k1_xboole_0)
% 3.68/1.01      | k1_xboole_0 != k1_xboole_0
% 3.68/1.01      | v1_funct_2(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_6467]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3003,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8838,plain,
% 3.68/1.01      ( X0 != X1 | X0 = sK1(X2,X3) | sK1(X2,X3) != X1 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_3003]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8839,plain,
% 3.68/1.01      ( sK1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.68/1.01      | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0)
% 3.68/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_8838]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4621,plain,
% 3.68/1.01      ( u1_struct_0(sK3) = k1_xboole_0
% 3.68/1.01      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_4433,c_3797]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4718,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 3.68/1.01      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.68/1.01      | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_4621,c_4510]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4622,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 3.68/1.01      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_4510,c_3797]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3779,plain,
% 3.68/1.01      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5304,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) = iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_4622,c_3779]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6297,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_4621,c_6292]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3,plain,
% 3.68/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.68/1.01      inference(cnf_transformation,[],[f117]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6298,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_6297,c_3]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_134,plain,
% 3.68/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_136,plain,
% 3.68/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_134]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3006,plain,
% 3.68/1.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.68/1.01      theory(equality) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3019,plain,
% 3.68/1.01      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
% 3.68/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_3006]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3007,plain,
% 3.68/1.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.68/1.01      theory(equality) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4498,plain,
% 3.68/1.01      ( ~ m1_subset_1(X0,X1)
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(X2))
% 3.68/1.01      | k1_zfmisc_1(X2) != X1
% 3.68/1.01      | sK5 != X0 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_3007]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5867,plain,
% 3.68/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.68/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 3.68/1.01      | k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
% 3.68/1.01      | sK5 != k1_xboole_0 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_4498]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5868,plain,
% 3.68/1.01      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X1)
% 3.68/1.01      | sK5 != k1_xboole_0
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(X0)) = iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_5867]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_5870,plain,
% 3.68/1.01      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 3.68/1.01      | sK5 != k1_xboole_0
% 3.68/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_5868]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6695,plain,
% 3.68/1.01      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_6298,c_136,c_137,c_138,c_3019,c_5870,c_6025,c_6552]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6696,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_6695]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6701,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.68/1.01      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_4621,c_6696]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8256,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 3.68/1.01      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_4718,c_5304,c_6701]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8257,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 3.68/1.01      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_8256]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_8258,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | u1_struct_0(sK2) = k1_xboole_0 ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_8257,c_7056,c_8095]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9427,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_xboole_0
% 3.68/1.01      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_6701,c_7056,c_8095]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9430,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_xboole_0
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_8258,c_9427]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9497,plain,
% 3.68/1.01      ( u1_struct_0(sK2) = k1_xboole_0 ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_8971,c_100,c_137,c_138,c_141,c_145,c_5468,c_6469,
% 3.68/1.01                 c_8839,c_9430]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7078,plain,
% 3.68/1.01      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,sK3) = iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_7056,c_3802]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9503,plain,
% 3.68/1.01      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,sK3) = iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_9497,c_7078]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7081,plain,
% 3.68/1.01      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_7056,c_3779]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9505,plain,
% 3.68/1.01      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_9497,c_7081]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7067,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 3.68/1.01      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0) ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_7056,c_4622]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10252,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 3.68/1.01      | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0 ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_7067,c_8095,c_9497]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3786,plain,
% 3.68/1.01      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(X2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9516,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_9497,c_3786]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9538,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_9516,c_9497]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9539,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_9538,c_4]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10698,plain,
% 3.68/1.01      ( l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_9539,c_47,c_48]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10699,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_10698]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10707,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_10252,c_10699]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10708,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_10707,c_3]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3924,plain,
% 3.68/1.01      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 3.68/1.01      | ~ v2_pre_topc(sK3)
% 3.68/1.01      | ~ l1_pre_topc(sK3) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_29]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3925,plain,
% 3.68/1.01      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_3924]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4002,plain,
% 3.68/1.01      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_27]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4003,plain,
% 3.68/1.01      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_4002]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4172,plain,
% 3.68/1.01      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 3.68/1.01      | ~ l1_pre_topc(sK3) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4173,plain,
% 3.68/1.01      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_4172]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10952,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_10708,c_49,c_50,c_3925,c_4003,c_4173]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10959,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_9505,c_10952]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3785,plain,
% 3.68/1.01      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(X2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9517,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_9497,c_3785]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9536,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_9517,c_9497]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9537,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_9536,c_4]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10675,plain,
% 3.68/1.01      ( l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_9537,c_47,c_48]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10676,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_10675]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10684,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_10252,c_10676]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10685,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_10684,c_3]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10937,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_10685,c_49,c_50,c_3925,c_4003,c_4173]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10944,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_9505,c_10937]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_52,plain,
% 3.68/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3978,plain,
% 3.68/1.01      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_3003]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3979,plain,
% 3.68/1.01      ( sK5 != k1_xboole_0
% 3.68/1.01      | k1_xboole_0 = sK5
% 3.68/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_3978]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4053,plain,
% 3.68/1.01      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_3003]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4291,plain,
% 3.68/1.01      ( X0 = sK4 | X0 != sK5 | sK4 != sK5 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_4053]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_4292,plain,
% 3.68/1.01      ( sK4 != sK5 | k1_xboole_0 = sK4 | k1_xboole_0 != sK5 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_4291]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6461,plain,
% 3.68/1.01      ( v1_funct_2(X0,X1,X2)
% 3.68/1.01      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.68/1.01      | X2 != u1_struct_0(sK3)
% 3.68/1.01      | X1 != u1_struct_0(sK2)
% 3.68/1.01      | X0 != sK4 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_3010]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6964,plain,
% 3.68/1.01      ( v1_funct_2(X0,X1,u1_struct_0(sK3))
% 3.68/1.01      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.68/1.01      | X1 != u1_struct_0(sK2)
% 3.68/1.01      | X0 != sK4
% 3.68/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_6461]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6965,plain,
% 3.68/1.01      ( X0 != u1_struct_0(sK2)
% 3.68/1.01      | X1 != sK4
% 3.68/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.68/1.01      | v1_funct_2(X1,X0,u1_struct_0(sK3)) = iProver_top
% 3.68/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_6964]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_6967,plain,
% 3.68/1.01      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.68/1.01      | k1_xboole_0 != u1_struct_0(sK2)
% 3.68/1.01      | k1_xboole_0 != sK4
% 3.68/1.01      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) = iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_6965]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3002,plain,( X0 = X0 ),theory(equality) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7294,plain,
% 3.68/1.01      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_3002]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7991,plain,
% 3.68/1.01      ( X0 != X1 | X0 = u1_struct_0(sK2) | u1_struct_0(sK2) != X1 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_3003]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7992,plain,
% 3.68/1.01      ( u1_struct_0(sK2) != k1_xboole_0
% 3.68/1.01      | k1_xboole_0 = u1_struct_0(sK2)
% 3.68/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_7991]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_7079,plain,
% 3.68/1.01      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,sK3) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_7056,c_3803]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9504,plain,
% 3.68/1.01      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,sK3) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_9497,c_7079]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_3784,plain,
% 3.68/1.01      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(X2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9518,plain,
% 3.68/1.01      ( v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_9497,c_3784]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9534,plain,
% 3.68/1.01      ( v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_9518,c_9497]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9535,plain,
% 3.68/1.01      ( v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_9534,c_4]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10166,plain,
% 3.68/1.01      ( l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_9535,c_47,c_48]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10167,plain,
% 3.68/1.01      ( v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_10166]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10269,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,sK3) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,k1_xboole_0) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_10252,c_10167]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10315,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,sK3) = iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_10269]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10940,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_10937]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11222,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_10944,c_49,c_50,c_52,c_36,c_100,c_124,c_136,c_137,
% 3.68/1.01                 c_138,c_141,c_145,c_3979,c_4292,c_5468,c_6026,c_6469,
% 3.68/1.01                 c_6967,c_7050,c_7294,c_7992,c_8839,c_9430,c_9504,c_9505,
% 3.68/1.01                 c_10315,c_10940]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10955,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_10952]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10276,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_10252,c_3783]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10278,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_10276,c_3]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11108,plain,
% 3.68/1.01      ( l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_10278,c_49,c_50]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11109,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,X1,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_11108]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11116,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_9497,c_11109]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11119,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_11116,c_9497]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11120,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_11119,c_4]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11134,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_11120,c_47,c_48]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11137,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(instantiation,[status(thm)],[c_11134]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11226,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_11222,c_52,c_36,c_100,c_124,c_136,c_137,c_138,c_141,
% 3.68/1.01                 c_145,c_3979,c_4292,c_5468,c_6026,c_6469,c_6967,c_7050,
% 3.68/1.01                 c_7294,c_7992,c_8839,c_9430,c_9503,c_9505,c_10955,
% 3.68/1.01                 c_11137]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11230,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_10252,c_11226]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11426,plain,
% 3.68/1.01      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2))) = k1_xboole_0 ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_10959,c_100,c_137,c_138,c_141,c_145,c_5468,c_6469,
% 3.68/1.01                 c_8839,c_11230]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11428,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_11426,c_10699]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11436,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_11428,c_4]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11830,plain,
% 3.68/1.01      ( v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,sK3) = iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_9503,c_11436]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11429,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_11426,c_10676]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11435,plain,
% 3.68/1.01      ( v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK2)),X1) = iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_11429,c_4]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11697,plain,
% 3.68/1.01      ( v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_11435,c_9504]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11432,plain,
% 3.68/1.01      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_11426,c_9505]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9519,plain,
% 3.68/1.01      ( v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_9497,c_3783]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9532,plain,
% 3.68/1.01      ( v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(light_normalisation,[status(thm)],[c_9519,c_9497]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_9533,plain,
% 3.68/1.01      ( v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK2) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(demodulation,[status(thm)],[c_9532,c_4]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10108,plain,
% 3.68/1.01      ( l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(global_propositional_subsumption,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_9533,c_47,c_48]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_10109,plain,
% 3.68/1.01      ( v5_pre_topc(X0,sK2,X1) != iProver_top
% 3.68/1.01      | v5_pre_topc(X0,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) != iProver_top
% 3.68/1.01      | v1_funct_2(X0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != iProver_top
% 3.68/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(X1) != iProver_top
% 3.68/1.01      | l1_pre_topc(X1) != iProver_top
% 3.68/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.68/1.01      inference(renaming,[status(thm)],[c_10108]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11526,plain,
% 3.68/1.01      ( v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,sK3) != iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_11432,c_10109]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(c_11525,plain,
% 3.68/1.01      ( v5_pre_topc(k1_xboole_0,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 3.68/1.01      | v5_pre_topc(k1_xboole_0,sK2,sK3) = iProver_top
% 3.68/1.01      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK3)) != iProver_top
% 3.68/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.68/1.01      | v2_pre_topc(sK3) != iProver_top
% 3.68/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.68/1.01      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 3.68/1.01      inference(superposition,[status(thm)],[c_11432,c_10167]) ).
% 3.68/1.01  
% 3.68/1.01  cnf(contradiction,plain,
% 3.68/1.01      ( $false ),
% 3.68/1.01      inference(minisat,
% 3.68/1.01                [status(thm)],
% 3.68/1.01                [c_11830,c_11697,c_11526,c_11525,c_11432,c_9430,c_8839,
% 3.68/1.01                 c_7992,c_7294,c_7056,c_6967,c_6469,c_5468,c_4292,c_4173,
% 3.68/1.01                 c_4003,c_3979,c_3925,c_145,c_141,c_138,c_137,c_136,
% 3.68/1.01                 c_124,c_100,c_36,c_52,c_50,c_49]) ).
% 3.68/1.01  
% 3.68/1.01  
% 3.68/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/1.01  
% 3.68/1.01  ------                               Statistics
% 3.68/1.01  
% 3.68/1.01  ------ General
% 3.68/1.01  
% 3.68/1.01  abstr_ref_over_cycles:                  0
% 3.68/1.01  abstr_ref_under_cycles:                 0
% 3.68/1.01  gc_basic_clause_elim:                   0
% 3.68/1.01  forced_gc_time:                         0
% 3.68/1.01  parsing_time:                           0.008
% 3.68/1.01  unif_index_cands_time:                  0.
% 3.68/1.01  unif_index_add_time:                    0.
% 3.68/1.01  orderings_time:                         0.
% 3.68/1.01  out_proof_time:                         0.025
% 3.68/1.01  total_time:                             0.445
% 3.68/1.01  num_of_symbols:                         56
% 3.68/1.01  num_of_terms:                           10252
% 3.68/1.01  
% 3.68/1.01  ------ Preprocessing
% 3.68/1.01  
% 3.68/1.01  num_of_splits:                          0
% 3.68/1.01  num_of_split_atoms:                     0
% 3.68/1.01  num_of_reused_defs:                     0
% 3.68/1.01  num_eq_ax_congr_red:                    19
% 3.68/1.01  num_of_sem_filtered_clauses:            1
% 3.68/1.01  num_of_subtypes:                        0
% 3.68/1.01  monotx_restored_types:                  0
% 3.68/1.01  sat_num_of_epr_types:                   0
% 3.68/1.01  sat_num_of_non_cyclic_types:            0
% 3.68/1.01  sat_guarded_non_collapsed_types:        0
% 3.68/1.01  num_pure_diseq_elim:                    0
% 3.68/1.01  simp_replaced_by:                       0
% 3.68/1.01  res_preprocessed:                       194
% 3.68/1.01  prep_upred:                             0
% 3.68/1.01  prep_unflattend:                        61
% 3.68/1.01  smt_new_axioms:                         0
% 3.68/1.01  pred_elim_cands:                        7
% 3.68/1.01  pred_elim:                              4
% 3.68/1.01  pred_elim_cl:                           7
% 3.68/1.01  pred_elim_cycles:                       8
% 3.68/1.01  merged_defs:                            8
% 3.68/1.01  merged_defs_ncl:                        0
% 3.68/1.01  bin_hyper_res:                          8
% 3.68/1.01  prep_cycles:                            4
% 3.68/1.01  pred_elim_time:                         0.03
% 3.68/1.01  splitting_time:                         0.
% 3.68/1.01  sem_filter_time:                        0.
% 3.68/1.01  monotx_time:                            0.
% 3.68/1.01  subtype_inf_time:                       0.
% 3.68/1.01  
% 3.68/1.01  ------ Problem properties
% 3.68/1.01  
% 3.68/1.01  clauses:                                39
% 3.68/1.01  conjectures:                            13
% 3.68/1.01  epr:                                    10
% 3.68/1.01  horn:                                   34
% 3.68/1.01  ground:                                 14
% 3.68/1.01  unary:                                  18
% 3.68/1.01  binary:                                 10
% 3.68/1.01  lits:                                   108
% 3.68/1.01  lits_eq:                                17
% 3.68/1.01  fd_pure:                                0
% 3.68/1.01  fd_pseudo:                              0
% 3.68/1.01  fd_cond:                                6
% 3.68/1.01  fd_pseudo_cond:                         2
% 3.68/1.01  ac_symbols:                             0
% 3.68/1.01  
% 3.68/1.01  ------ Propositional Solver
% 3.68/1.01  
% 3.68/1.01  prop_solver_calls:                      34
% 3.68/1.01  prop_fast_solver_calls:                 2694
% 3.68/1.01  smt_solver_calls:                       0
% 3.68/1.01  smt_fast_solver_calls:                  0
% 3.68/1.01  prop_num_of_clauses:                    4616
% 3.68/1.01  prop_preprocess_simplified:             9466
% 3.68/1.01  prop_fo_subsumed:                       131
% 3.68/1.01  prop_solver_time:                       0.
% 3.68/1.01  smt_solver_time:                        0.
% 3.68/1.01  smt_fast_solver_time:                   0.
% 3.68/1.01  prop_fast_solver_time:                  0.
% 3.68/1.01  prop_unsat_core_time:                   0.
% 3.68/1.01  
% 3.68/1.01  ------ QBF
% 3.68/1.01  
% 3.68/1.01  qbf_q_res:                              0
% 3.68/1.01  qbf_num_tautologies:                    0
% 3.68/1.01  qbf_prep_cycles:                        0
% 3.68/1.01  
% 3.68/1.01  ------ BMC1
% 3.68/1.01  
% 3.68/1.01  bmc1_current_bound:                     -1
% 3.68/1.01  bmc1_last_solved_bound:                 -1
% 3.68/1.01  bmc1_unsat_core_size:                   -1
% 3.68/1.01  bmc1_unsat_core_parents_size:           -1
% 3.68/1.01  bmc1_merge_next_fun:                    0
% 3.68/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.68/1.01  
% 3.68/1.01  ------ Instantiation
% 3.68/1.01  
% 3.68/1.01  inst_num_of_clauses:                    1298
% 3.68/1.01  inst_num_in_passive:                    334
% 3.68/1.01  inst_num_in_active:                     678
% 3.68/1.01  inst_num_in_unprocessed:                287
% 3.68/1.01  inst_num_of_loops:                      770
% 3.68/1.01  inst_num_of_learning_restarts:          0
% 3.68/1.01  inst_num_moves_active_passive:          85
% 3.68/1.01  inst_lit_activity:                      0
% 3.68/1.01  inst_lit_activity_moves:                0
% 3.68/1.01  inst_num_tautologies:                   0
% 3.68/1.01  inst_num_prop_implied:                  0
% 3.68/1.01  inst_num_existing_simplified:           0
% 3.68/1.01  inst_num_eq_res_simplified:             0
% 3.68/1.01  inst_num_child_elim:                    0
% 3.68/1.01  inst_num_of_dismatching_blockings:      248
% 3.68/1.01  inst_num_of_non_proper_insts:           1215
% 3.68/1.01  inst_num_of_duplicates:                 0
% 3.68/1.01  inst_inst_num_from_inst_to_res:         0
% 3.68/1.01  inst_dismatching_checking_time:         0.
% 3.68/1.01  
% 3.68/1.01  ------ Resolution
% 3.68/1.01  
% 3.68/1.01  res_num_of_clauses:                     0
% 3.68/1.01  res_num_in_passive:                     0
% 3.68/1.01  res_num_in_active:                      0
% 3.68/1.01  res_num_of_loops:                       198
% 3.68/1.01  res_forward_subset_subsumed:            50
% 3.68/1.01  res_backward_subset_subsumed:           4
% 3.68/1.01  res_forward_subsumed:                   0
% 3.68/1.01  res_backward_subsumed:                  0
% 3.68/1.01  res_forward_subsumption_resolution:     3
% 3.68/1.01  res_backward_subsumption_resolution:    0
% 3.68/1.01  res_clause_to_clause_subsumption:       907
% 3.68/1.01  res_orphan_elimination:                 0
% 3.68/1.01  res_tautology_del:                      130
% 3.68/1.01  res_num_eq_res_simplified:              0
% 3.68/1.01  res_num_sel_changes:                    0
% 3.68/1.01  res_moves_from_active_to_pass:          0
% 3.68/1.01  
% 3.68/1.01  ------ Superposition
% 3.68/1.01  
% 3.68/1.01  sup_time_total:                         0.
% 3.68/1.01  sup_time_generating:                    0.
% 3.68/1.01  sup_time_sim_full:                      0.
% 3.68/1.01  sup_time_sim_immed:                     0.
% 3.68/1.01  
% 3.68/1.01  sup_num_of_clauses:                     153
% 3.68/1.01  sup_num_in_active:                      55
% 3.68/1.01  sup_num_in_passive:                     98
% 3.68/1.01  sup_num_of_loops:                       153
% 3.68/1.01  sup_fw_superposition:                   237
% 3.68/1.01  sup_bw_superposition:                   193
% 3.68/1.01  sup_immediate_simplified:               145
% 3.68/1.01  sup_given_eliminated:                   0
% 3.68/1.01  comparisons_done:                       0
% 3.68/1.01  comparisons_avoided:                    13
% 3.68/1.01  
% 3.68/1.01  ------ Simplifications
% 3.68/1.01  
% 3.68/1.01  
% 3.68/1.01  sim_fw_subset_subsumed:                 56
% 3.68/1.01  sim_bw_subset_subsumed:                 166
% 3.68/1.01  sim_fw_subsumed:                        12
% 3.68/1.01  sim_bw_subsumed:                        1
% 3.68/1.01  sim_fw_subsumption_res:                 0
% 3.68/1.01  sim_bw_subsumption_res:                 0
% 3.68/1.01  sim_tautology_del:                      5
% 3.68/1.01  sim_eq_tautology_del:                   25
% 3.68/1.01  sim_eq_res_simp:                        0
% 3.68/1.01  sim_fw_demodulated:                     61
% 3.68/1.01  sim_bw_demodulated:                     52
% 3.68/1.01  sim_light_normalised:                   67
% 3.68/1.01  sim_joinable_taut:                      0
% 3.68/1.01  sim_joinable_simp:                      0
% 3.68/1.01  sim_ac_normalised:                      0
% 3.68/1.01  sim_smt_subsumption:                    0
% 3.68/1.01  
%------------------------------------------------------------------------------
