%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:52 EST 2020

% Result     : Theorem 11.61s
% Output     : CNFRefutation 11.61s
% Verified   : 
% Statistics : Number of formulae       :  427 (69979 expanded)
%              Number of clauses        :  304 (18396 expanded)
%              Number of leaves         :   30 (19124 expanded)
%              Depth                    :   34
%              Number of atoms          : 1821 (676553 expanded)
%              Number of equality atoms :  928 (84817 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,conjecture,(
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

fof(f36,negated_conjecture,(
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
    inference(negated_conjecture,[],[f35])).

fof(f75,plain,(
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
    inference(ennf_transformation,[],[f36])).

fof(f76,plain,(
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
    inference(flattening,[],[f75])).

fof(f107,plain,(
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
    inference(nnf_transformation,[],[f76])).

fof(f108,plain,(
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
    inference(flattening,[],[f107])).

fof(f112,plain,(
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
     => ( ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ v5_pre_topc(X2,X0,X1) )
        & ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | v5_pre_topc(X2,X0,X1) )
        & sK9 = X2
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
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
              | ~ v5_pre_topc(sK8,X0,X1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | v5_pre_topc(sK8,X0,X1) )
            & sK8 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
            & v1_funct_1(X3) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
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
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
                  | ~ v5_pre_topc(X2,X0,sK7) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
                  | v5_pre_topc(X2,X0,sK7) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK7)
        & v2_pre_topc(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK6,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK6,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f113,plain,
    ( ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
      | ~ v5_pre_topc(sK8,sK6,sK7) )
    & ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
      | v5_pre_topc(sK8,sK6,sK7) )
    & sK8 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    & v1_funct_1(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f108,f112,f111,f110,f109])).

fof(f188,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f113])).

fof(f192,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f113])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f55])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f57])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f156,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f189,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f113])).

fof(f187,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f113])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f120,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f191,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) ),
    inference(cnf_transformation,[],[f113])).

fof(f190,plain,(
    v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
    inference(cnf_transformation,[],[f113])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f142,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f61])).

fof(f168,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f85])).

fof(f123,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f91])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f92])).

fof(f199,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f131])).

fof(f143,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f166,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f92])).

fof(f200,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f130])).

fof(f135,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f196,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f121])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f193,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f113])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f51])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f34,axiom,(
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

fof(f73,plain,(
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
    inference(ennf_transformation,[],[f34])).

fof(f74,plain,(
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
    inference(flattening,[],[f73])).

fof(f106,plain,(
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
    inference(nnf_transformation,[],[f74])).

fof(f181,plain,(
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
    inference(cnf_transformation,[],[f106])).

fof(f204,plain,(
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
    inference(equality_resolution,[],[f181])).

fof(f184,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f113])).

fof(f185,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f113])).

fof(f182,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f113])).

fof(f183,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f113])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f176,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f32])).

fof(f69,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f69])).

fof(f177,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f175,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f33,axiom,(
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

fof(f71,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f72,plain,(
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
    inference(flattening,[],[f71])).

fof(f105,plain,(
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
    inference(nnf_transformation,[],[f72])).

fof(f179,plain,(
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
    inference(cnf_transformation,[],[f105])).

fof(f202,plain,(
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
    inference(equality_resolution,[],[f179])).

fof(f180,plain,(
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
    inference(cnf_transformation,[],[f106])).

fof(f205,plain,(
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
    inference(equality_resolution,[],[f180])).

fof(f194,plain,
    ( ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f113])).

fof(f178,plain,(
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
    inference(cnf_transformation,[],[f105])).

fof(f203,plain,(
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
    inference(equality_resolution,[],[f178])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f25,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK4(X0,X1),X0,X1)
        & v1_funct_1(sK4(X0,X1))
        & v5_relat_1(sK4(X0,X1),X1)
        & v4_relat_1(sK4(X0,X1),X0)
        & v1_relat_1(sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK4(X0,X1),X0,X1)
      & v1_funct_1(sK4(X0,X1))
      & v5_relat_1(sK4(X0,X1),X1)
      & v4_relat_1(sK4(X0,X1),X0)
      & v1_relat_1(sK4(X0,X1))
      & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f99])).

fof(f162,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f100])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f119,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f158,plain,(
    ! [X0,X1] : m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f100])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_74,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f188])).

cnf(c_5643,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_70,negated_conjecture,
    ( sK8 = sK9 ),
    inference(cnf_transformation,[],[f192])).

cnf(c_5739,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5643,c_70])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_43,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f156])).

cnf(c_986,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_40,c_43])).

cnf(c_32,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_988,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_986,c_32,c_30])).

cnf(c_989,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_988])).

cnf(c_5632,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_6821,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5739,c_5632])).

cnf(c_73,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f189])).

cnf(c_88,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_75,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f187])).

cnf(c_5642,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_5730,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5642,c_70])).

cnf(c_7151,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6821,c_88,c_5730])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_5688,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8037,plain,
    ( u1_struct_0(sK7) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_7151,c_5688])).

cnf(c_71,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) ),
    inference(cnf_transformation,[],[f191])).

cnf(c_5646,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_6820,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5646,c_5632])).

cnf(c_72,negated_conjecture,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
    inference(cnf_transformation,[],[f190])).

cnf(c_89,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_7248,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6820,c_88,c_89])).

cnf(c_8036,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_7248,c_5688])).

cnf(c_8737,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_8037,c_8036])).

cnf(c_8094,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8037,c_5646])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_5673,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_16391,plain,
    ( k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),sK9,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),sK9)
    | u1_struct_0(sK6) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_8094,c_5673])).

cnf(c_28254,plain,
    ( k8_relset_1(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),sK9,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),sK9)
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_8737,c_16391])).

cnf(c_29,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_54,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_5661,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_5678,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9382,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5646,c_5678])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_5687,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13102,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = sK9
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_9382,c_5687])).

cnf(c_15831,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = sK9
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_8036,c_13102])).

cnf(c_15,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f199])).

cnf(c_15842,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = sK9
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | r1_tarski(k1_xboole_0,sK9) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15831,c_15])).

cnf(c_28,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f143])).

cnf(c_50,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_5664,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_18557,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_5664])).

cnf(c_18599,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18557,c_29])).

cnf(c_16,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f200])).

cnf(c_18600,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18599,c_16])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_218,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_220,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f196])).

cnf(c_240,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_242,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_18836,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18600,c_220,c_242])).

cnf(c_24,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1016,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_32,c_24])).

cnf(c_1020,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1016,c_30])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_1020])).

cnf(c_5631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_6414,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_5631])).

cnf(c_18843,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18836,c_6414])).

cnf(c_18870,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18843,c_29])).

cnf(c_23791,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = sK9
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15842,c_18870])).

cnf(c_23792,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0) = sK9
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_8036,c_23791])).

cnf(c_24028,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | sK9 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23792,c_15])).

cnf(c_69,negated_conjecture,
    ( v5_pre_topc(sK8,sK6,sK7)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    inference(cnf_transformation,[],[f193])).

cnf(c_5647,plain,
    ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_5886,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5647,c_70])).

cnf(c_5645,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_5674,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_21966,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top
    | r1_tarski(k1_relat_1(sK9),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5646,c_5674])).

cnf(c_66,plain,
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
    inference(cnf_transformation,[],[f204])).

cnf(c_5650,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_23071,plain,
    ( v5_pre_topc(sK9,X0,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,X0,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_21966,c_5650])).

cnf(c_78,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f184])).

cnf(c_83,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_77,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f185])).

cnf(c_84,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_27513,plain,
    ( v2_pre_topc(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v5_pre_topc(sK9,X0,sK7) = iProver_top
    | v5_pre_topc(sK9,X0,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23071,c_83,c_84,c_88])).

cnf(c_27514,plain,
    ( v5_pre_topc(sK9,X0,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,X0,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_27513])).

cnf(c_21967,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK7)))) = iProver_top
    | r1_tarski(k1_relat_1(sK9),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5739,c_5674])).

cnf(c_27527,plain,
    ( v5_pre_topc(sK9,X0,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,X0,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27514,c_21967])).

cnf(c_27531,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5645,c_27527])).

cnf(c_80,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f182])).

cnf(c_81,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_79,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f183])).

cnf(c_82,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_90,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_62,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f176])).

cnf(c_6248,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_6249,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6248])).

cnf(c_63,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f177])).

cnf(c_6275,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_6276,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6275])).

cnf(c_6350,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_6351,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6350])).

cnf(c_61,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f175])).

cnf(c_6640,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_6641,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6640])).

cnf(c_27639,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27531,c_81,c_82,c_90,c_6249,c_6276,c_6351,c_6641])).

cnf(c_27640,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_27639])).

cnf(c_27649,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5886,c_27640])).

cnf(c_27816,plain,
    ( sK9 = k1_xboole_0
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24028,c_27649])).

cnf(c_64,plain,
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
    inference(cnf_transformation,[],[f202])).

cnf(c_5652,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_22726,plain,
    ( v5_pre_topc(sK9,X0,sK7) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_21967,c_5652])).

cnf(c_28059,plain,
    ( v2_pre_topc(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) != iProver_top
    | v5_pre_topc(sK9,X0,sK7) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22726,c_83,c_84,c_88])).

cnf(c_28060,plain,
    ( v5_pre_topc(sK9,X0,sK7) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_28059])).

cnf(c_28073,plain,
    ( sK9 = k1_xboole_0
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_24028,c_28060])).

cnf(c_32039,plain,
    ( sK9 = k1_xboole_0
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27816,c_81,c_82,c_90,c_5730,c_5739,c_6351,c_28073])).

cnf(c_67,plain,
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
    inference(cnf_transformation,[],[f205])).

cnf(c_5649,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_8527,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5646,c_5649])).

cnf(c_8696,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8527,c_81,c_82,c_83,c_84,c_88,c_89,c_6249,c_6276,c_6641])).

cnf(c_8697,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8696])).

cnf(c_8704,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8037,c_8697])).

cnf(c_8705,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8704,c_15])).

cnf(c_22733,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21967,c_8697])).

cnf(c_25617,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8705,c_90,c_6351,c_22733])).

cnf(c_25618,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_25617])).

cnf(c_68,negated_conjecture,
    ( ~ v5_pre_topc(sK8,sK6,sK7)
    | ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    inference(cnf_transformation,[],[f194])).

cnf(c_5648,plain,
    ( v5_pre_topc(sK8,sK6,sK7) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_5903,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5648,c_70])).

cnf(c_25627,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25618,c_5903])).

cnf(c_25659,plain,
    ( sK9 = k1_xboole_0
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24028,c_25627])).

cnf(c_65,plain,
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
    inference(cnf_transformation,[],[f203])).

cnf(c_5651,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_22727,plain,
    ( v5_pre_topc(sK9,X0,sK7) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_21967,c_5651])).

cnf(c_29612,plain,
    ( v2_pre_topc(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) = iProver_top
    | v5_pre_topc(sK9,X0,sK7) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22727,c_83,c_84,c_88])).

cnf(c_29613,plain,
    ( v5_pre_topc(sK9,X0,sK7) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_29612])).

cnf(c_29627,plain,
    ( sK9 = k1_xboole_0
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_24028,c_29613])).

cnf(c_32043,plain,
    ( sK9 = k1_xboole_0
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32039,c_81,c_82,c_90,c_5730,c_5739,c_6351,c_25659,c_29627])).

cnf(c_32049,plain,
    ( sK9 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5661,c_32043])).

cnf(c_6260,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_6261,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6260])).

cnf(c_31,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_26,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_948,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_31,c_26])).

cnf(c_952,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_30])).

cnf(c_953,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_952])).

cnf(c_5634,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_953])).

cnf(c_8144,plain,
    ( r1_tarski(k2_relat_1(sK9),u1_struct_0(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5739,c_5634])).

cnf(c_38544,plain,
    ( sK9 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32049,c_88,c_90,c_6261,c_8144])).

cnf(c_55980,plain,
    ( k8_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),k1_xboole_0)
    | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_28254,c_29,c_38544])).

cnf(c_45,plain,
    ( v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_155,plain,
    ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_157,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_4187,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6287,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK4(X1,X2))
    | X0 != sK4(X1,X2) ),
    inference(instantiation,[status(thm)],[c_4187])).

cnf(c_6288,plain,
    ( X0 != sK4(X1,X2)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK4(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6287])).

cnf(c_6290,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6288])).

cnf(c_49,plain,
    ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_5665,plain,
    ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_8184,plain,
    ( m1_subset_1(sK4(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_5665])).

cnf(c_9387,plain,
    ( r1_tarski(sK4(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8184,c_5678])).

cnf(c_9419,plain,
    ( r1_tarski(sK4(X0,k1_xboole_0),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9387])).

cnf(c_9421,plain,
    ( r1_tarski(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9419])).

cnf(c_11569,plain,
    ( ~ v1_xboole_0(sK4(X0,X1))
    | k1_xboole_0 = sK4(X0,X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_11573,plain,
    ( ~ v1_xboole_0(sK4(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11569])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_578,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_579,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_578])).

cnf(c_704,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_19,c_579])).

cnf(c_26537,plain,
    ( ~ r1_tarski(sK4(X0,X1),X2)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(sK4(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_26544,plain,
    ( ~ r1_tarski(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(sK4(k1_xboole_0,k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_26537])).

cnf(c_20268,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_5661])).

cnf(c_20269,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20268,c_28])).

cnf(c_5676,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_5676])).

cnf(c_10251,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10230])).

cnf(c_20616,plain,
    ( v1_funct_1(k1_xboole_0) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20269,c_220,c_242,c_10251,c_18870])).

cnf(c_20617,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_20616])).

cnf(c_8092,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_8037,c_5886])).

cnf(c_9190,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5646,c_5650])).

cnf(c_9751,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9190,c_81,c_82,c_83,c_84,c_88,c_89,c_6249,c_6276,c_6641])).

cnf(c_9752,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9751])).

cnf(c_9760,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8037,c_9752])).

cnf(c_8093,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8037,c_5903])).

cnf(c_8096,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8037,c_5739])).

cnf(c_8104,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8096,c_15])).

cnf(c_9759,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5886,c_9752])).

cnf(c_9799,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8037,c_9759])).

cnf(c_9805,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9799,c_15])).

cnf(c_10789,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
    | u1_struct_0(sK6) = k1_relat_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9760,c_8093,c_8104,c_9805])).

cnf(c_10790,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10789])).

cnf(c_10797,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8092,c_10790])).

cnf(c_28265,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8737,c_10797])).

cnf(c_5679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9460,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5679,c_8697])).

cnf(c_9828,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9460,c_5903])).

cnf(c_9878,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8037,c_9828])).

cnf(c_9879,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(sK9,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9878,c_15])).

cnf(c_9386,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | r1_tarski(sK9,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8104,c_5678])).

cnf(c_20005,plain,
    ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | u1_struct_0(sK6) = k1_relat_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9879,c_9386])).

cnf(c_20006,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_20005])).

cnf(c_28247,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8737,c_20006])).

cnf(c_28230,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8737,c_28060])).

cnf(c_28530,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28230,c_28265])).

cnf(c_29626,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8737,c_29613])).

cnf(c_55942,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(sK9)
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28265,c_81,c_82,c_90,c_5730,c_5739,c_6351,c_28247,c_28530,c_29626])).

cnf(c_55946,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_55942,c_29,c_38544])).

cnf(c_55951,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20617,c_55946])).

cnf(c_55984,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_55980,c_157,c_5,c_6290,c_9421,c_11573,c_26544,c_55951])).

cnf(c_9384,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8094,c_5678])).

cnf(c_13113,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = sK9
    | u1_struct_0(sK6) = k1_relat_1(sK9)
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_9384,c_5687])).

cnf(c_55331,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13113,c_29,c_38544])).

cnf(c_56034,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_55984,c_55331])).

cnf(c_56110,plain,
    ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_56034,c_15])).

cnf(c_38713,plain,
    ( u1_struct_0(sK7) = k1_xboole_0
    | u1_struct_0(sK6) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_38544,c_8037])).

cnf(c_38762,plain,
    ( u1_struct_0(sK7) = k1_xboole_0
    | u1_struct_0(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_38713,c_29])).

cnf(c_38720,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38544,c_5646])).

cnf(c_43510,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38720,c_5649])).

cnf(c_21970,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_5674])).

cnf(c_22117,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21970,c_6414])).

cnf(c_22118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_22117])).

cnf(c_43509,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38720,c_5650])).

cnf(c_6548,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),X1)
    | v5_pre_topc(X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_7276,plain,
    ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | v5_pre_topc(X0,sK6,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_6548])).

cnf(c_7277,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(X0,sK6,sK7) = iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7276])).

cnf(c_7279,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7277])).

cnf(c_6558,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),X1)
    | ~ v5_pre_topc(X0,sK6,X1)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_7316,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
    | ~ v5_pre_topc(X0,sK6,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_6558])).

cnf(c_7317,plain,
    ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(X0,sK6,sK7) != iProver_top
    | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7316])).

cnf(c_7319,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7317])).

cnf(c_38595,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38544,c_27649])).

cnf(c_38615,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38544,c_25627])).

cnf(c_38722,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38544,c_5739])).

cnf(c_38723,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38544,c_5730])).

cnf(c_44729,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43509,c_81,c_82,c_83,c_84,c_157,c_5,c_6290,c_7279,c_7319,c_9421,c_11573,c_26544,c_38595,c_38615,c_38722,c_38723])).

cnf(c_44730,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_44729])).

cnf(c_44733,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44730,c_81,c_82,c_83,c_84,c_157,c_5,c_6290,c_7279,c_9421,c_11573,c_26544,c_38615,c_38722,c_38723])).

cnf(c_44740,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22118,c_44733])).

cnf(c_44760,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43510,c_220,c_242,c_44740])).

cnf(c_44765,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38762,c_44760])).

cnf(c_8095,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8037,c_5645])).

cnf(c_38708,plain,
    ( u1_struct_0(sK6) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38544,c_8095])).

cnf(c_38783,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38708,c_29])).

cnf(c_56044,plain,
    ( u1_struct_0(sK6) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_55984,c_38783])).

cnf(c_57478,plain,
    ( u1_struct_0(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_56110,c_44765,c_56044])).

cnf(c_43508,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38720,c_5651])).

cnf(c_43507,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38720,c_5652])).

cnf(c_6568,plain,
    ( v5_pre_topc(X0,sK6,X1)
    | ~ v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_7356,plain,
    ( ~ v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | v5_pre_topc(X0,sK6,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_6568])).

cnf(c_7357,plain,
    ( v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(X0,sK6,sK7) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7356])).

cnf(c_7359,plain,
    ( v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7357])).

cnf(c_6588,plain,
    ( ~ v5_pre_topc(X0,sK6,X1)
    | v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_7396,plain,
    ( v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v5_pre_topc(X0,sK6,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_6588])).

cnf(c_7397,plain,
    ( v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(X0,sK6,sK7) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7396])).

cnf(c_7399,plain,
    ( v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7397])).

cnf(c_10813,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5646,c_5652])).

cnf(c_6245,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_6246,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6245])).

cnf(c_6272,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_6273,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6272])).

cnf(c_6636,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_6637,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6636])).

cnf(c_11521,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10813,c_81,c_82,c_83,c_84,c_88,c_89,c_6246,c_6273,c_6637])).

cnf(c_11522,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11521])).

cnf(c_11532,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8037,c_11522])).

cnf(c_12671,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8036,c_11532])).

cnf(c_12689,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
    | u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12671,c_15])).

cnf(c_6359,plain,
    ( r1_tarski(k1_relat_1(sK9),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5739,c_5631])).

cnf(c_11531,plain,
    ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5886,c_11522])).

cnf(c_23078,plain,
    ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21966,c_11531])).

cnf(c_27112,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
    | u1_struct_0(sK6) = k1_relat_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12689,c_6359,c_8093,c_23078])).

cnf(c_27113,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_27112])).

cnf(c_27120,plain,
    ( u1_struct_0(sK6) = k1_relat_1(sK9)
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8092,c_27113])).

cnf(c_32153,plain,
    ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,sK7) = iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27120,c_6359,c_23078])).

cnf(c_38576,plain,
    ( v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38544,c_32153])).

cnf(c_23061,plain,
    ( r1_tarski(k1_relat_1(sK9),X0) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_21966,c_5678])).

cnf(c_9954,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5646,c_5651])).

cnf(c_10329,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9954,c_81,c_82,c_83,c_84,c_88,c_89,c_6246,c_6273,c_6637])).

cnf(c_10330,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10329])).

cnf(c_10337,plain,
    ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5679,c_10330])).

cnf(c_10432,plain,
    ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10337,c_5903])).

cnf(c_23667,plain,
    ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | r1_tarski(k1_relat_1(sK9),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23061,c_10432])).

cnf(c_25998,plain,
    ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23667,c_6359])).

cnf(c_25999,plain,
    ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(sK9,sK6,sK7) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_25998])).

cnf(c_38609,plain,
    ( v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38544,c_25999])).

cnf(c_44626,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43507,c_81,c_82,c_83,c_84,c_157,c_5,c_6290,c_7359,c_7399,c_9421,c_11573,c_26544,c_38576,c_38609,c_38722,c_38723])).

cnf(c_44627,plain,
    ( v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_44626])).

cnf(c_44630,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_44627,c_81,c_82,c_83,c_84,c_157,c_5,c_6290,c_7359,c_9421,c_11573,c_26544,c_38609,c_38722,c_38723])).

cnf(c_44637,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22118,c_44630])).

cnf(c_44657,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43508,c_220,c_242,c_44637])).

cnf(c_57518,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_57478,c_44657])).

cnf(c_24152,plain,
    ( sK9 = k1_xboole_0
    | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_24028,c_5645])).

cnf(c_6342,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
    | r1_tarski(k2_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_6343,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
    | r1_tarski(k2_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6342])).

cnf(c_6396,plain,
    ( v1_funct_2(sK9,k1_relat_1(sK9),X0)
    | ~ r1_tarski(k2_relat_1(sK9),X0)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_7057,plain,
    ( v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ r1_tarski(k2_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_6396])).

cnf(c_7058,plain,
    ( v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
    | r1_tarski(k2_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7057])).

cnf(c_24940,plain,
    ( v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24152,c_88,c_90,c_6261,c_6343,c_7058])).

cnf(c_38623,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38544,c_24940])).

cnf(c_39206,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38623,c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_57518,c_39206])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:23:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.33  % Running in FOF mode
% 11.61/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.61/1.98  
% 11.61/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.61/1.98  
% 11.61/1.98  ------  iProver source info
% 11.61/1.98  
% 11.61/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.61/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.61/1.98  git: non_committed_changes: false
% 11.61/1.98  git: last_make_outside_of_git: false
% 11.61/1.98  
% 11.61/1.98  ------ 
% 11.61/1.98  
% 11.61/1.98  ------ Input Options
% 11.61/1.98  
% 11.61/1.98  --out_options                           all
% 11.61/1.98  --tptp_safe_out                         true
% 11.61/1.98  --problem_path                          ""
% 11.61/1.98  --include_path                          ""
% 11.61/1.98  --clausifier                            res/vclausify_rel
% 11.61/1.98  --clausifier_options                    --mode clausify
% 11.61/1.98  --stdin                                 false
% 11.61/1.98  --stats_out                             all
% 11.61/1.98  
% 11.61/1.98  ------ General Options
% 11.61/1.98  
% 11.61/1.98  --fof                                   false
% 11.61/1.98  --time_out_real                         305.
% 11.61/1.98  --time_out_virtual                      -1.
% 11.61/1.98  --symbol_type_check                     false
% 11.61/1.98  --clausify_out                          false
% 11.61/1.98  --sig_cnt_out                           false
% 11.61/1.98  --trig_cnt_out                          false
% 11.61/1.98  --trig_cnt_out_tolerance                1.
% 11.61/1.98  --trig_cnt_out_sk_spl                   false
% 11.61/1.98  --abstr_cl_out                          false
% 11.61/1.98  
% 11.61/1.98  ------ Global Options
% 11.61/1.98  
% 11.61/1.98  --schedule                              default
% 11.61/1.98  --add_important_lit                     false
% 11.61/1.98  --prop_solver_per_cl                    1000
% 11.61/1.98  --min_unsat_core                        false
% 11.61/1.98  --soft_assumptions                      false
% 11.61/1.98  --soft_lemma_size                       3
% 11.61/1.98  --prop_impl_unit_size                   0
% 11.61/1.98  --prop_impl_unit                        []
% 11.61/1.98  --share_sel_clauses                     true
% 11.61/1.98  --reset_solvers                         false
% 11.61/1.98  --bc_imp_inh                            [conj_cone]
% 11.61/1.98  --conj_cone_tolerance                   3.
% 11.61/1.98  --extra_neg_conj                        none
% 11.61/1.98  --large_theory_mode                     true
% 11.61/1.98  --prolific_symb_bound                   200
% 11.61/1.98  --lt_threshold                          2000
% 11.61/1.98  --clause_weak_htbl                      true
% 11.61/1.98  --gc_record_bc_elim                     false
% 11.61/1.98  
% 11.61/1.98  ------ Preprocessing Options
% 11.61/1.98  
% 11.61/1.98  --preprocessing_flag                    true
% 11.61/1.98  --time_out_prep_mult                    0.1
% 11.61/1.98  --splitting_mode                        input
% 11.61/1.98  --splitting_grd                         true
% 11.61/1.98  --splitting_cvd                         false
% 11.61/1.98  --splitting_cvd_svl                     false
% 11.61/1.98  --splitting_nvd                         32
% 11.61/1.98  --sub_typing                            true
% 11.61/1.98  --prep_gs_sim                           true
% 11.61/1.98  --prep_unflatten                        true
% 11.61/1.98  --prep_res_sim                          true
% 11.61/1.98  --prep_upred                            true
% 11.61/1.98  --prep_sem_filter                       exhaustive
% 11.61/1.98  --prep_sem_filter_out                   false
% 11.61/1.98  --pred_elim                             true
% 11.61/1.98  --res_sim_input                         true
% 11.61/1.98  --eq_ax_congr_red                       true
% 11.61/1.98  --pure_diseq_elim                       true
% 11.61/1.98  --brand_transform                       false
% 11.61/1.98  --non_eq_to_eq                          false
% 11.61/1.98  --prep_def_merge                        true
% 11.61/1.98  --prep_def_merge_prop_impl              false
% 11.61/1.98  --prep_def_merge_mbd                    true
% 11.61/1.98  --prep_def_merge_tr_red                 false
% 11.61/1.98  --prep_def_merge_tr_cl                  false
% 11.61/1.98  --smt_preprocessing                     true
% 11.61/1.98  --smt_ac_axioms                         fast
% 11.61/1.98  --preprocessed_out                      false
% 11.61/1.98  --preprocessed_stats                    false
% 11.61/1.98  
% 11.61/1.98  ------ Abstraction refinement Options
% 11.61/1.98  
% 11.61/1.98  --abstr_ref                             []
% 11.61/1.98  --abstr_ref_prep                        false
% 11.61/1.98  --abstr_ref_until_sat                   false
% 11.61/1.98  --abstr_ref_sig_restrict                funpre
% 11.61/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.61/1.98  --abstr_ref_under                       []
% 11.61/1.98  
% 11.61/1.98  ------ SAT Options
% 11.61/1.98  
% 11.61/1.98  --sat_mode                              false
% 11.61/1.98  --sat_fm_restart_options                ""
% 11.61/1.98  --sat_gr_def                            false
% 11.61/1.98  --sat_epr_types                         true
% 11.61/1.98  --sat_non_cyclic_types                  false
% 11.61/1.98  --sat_finite_models                     false
% 11.61/1.98  --sat_fm_lemmas                         false
% 11.61/1.98  --sat_fm_prep                           false
% 11.61/1.98  --sat_fm_uc_incr                        true
% 11.61/1.98  --sat_out_model                         small
% 11.61/1.98  --sat_out_clauses                       false
% 11.61/1.98  
% 11.61/1.98  ------ QBF Options
% 11.61/1.98  
% 11.61/1.98  --qbf_mode                              false
% 11.61/1.98  --qbf_elim_univ                         false
% 11.61/1.98  --qbf_dom_inst                          none
% 11.61/1.98  --qbf_dom_pre_inst                      false
% 11.61/1.98  --qbf_sk_in                             false
% 11.61/1.98  --qbf_pred_elim                         true
% 11.61/1.98  --qbf_split                             512
% 11.61/1.98  
% 11.61/1.98  ------ BMC1 Options
% 11.61/1.98  
% 11.61/1.98  --bmc1_incremental                      false
% 11.61/1.98  --bmc1_axioms                           reachable_all
% 11.61/1.98  --bmc1_min_bound                        0
% 11.61/1.98  --bmc1_max_bound                        -1
% 11.61/1.98  --bmc1_max_bound_default                -1
% 11.61/1.98  --bmc1_symbol_reachability              true
% 11.61/1.98  --bmc1_property_lemmas                  false
% 11.61/1.98  --bmc1_k_induction                      false
% 11.61/1.98  --bmc1_non_equiv_states                 false
% 11.61/1.98  --bmc1_deadlock                         false
% 11.61/1.98  --bmc1_ucm                              false
% 11.61/1.98  --bmc1_add_unsat_core                   none
% 11.61/1.98  --bmc1_unsat_core_children              false
% 11.61/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.61/1.98  --bmc1_out_stat                         full
% 11.61/1.98  --bmc1_ground_init                      false
% 11.61/1.98  --bmc1_pre_inst_next_state              false
% 11.61/1.98  --bmc1_pre_inst_state                   false
% 11.61/1.98  --bmc1_pre_inst_reach_state             false
% 11.61/1.98  --bmc1_out_unsat_core                   false
% 11.61/1.98  --bmc1_aig_witness_out                  false
% 11.61/1.98  --bmc1_verbose                          false
% 11.61/1.98  --bmc1_dump_clauses_tptp                false
% 11.61/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.61/1.98  --bmc1_dump_file                        -
% 11.61/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.61/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.61/1.98  --bmc1_ucm_extend_mode                  1
% 11.61/1.98  --bmc1_ucm_init_mode                    2
% 11.61/1.98  --bmc1_ucm_cone_mode                    none
% 11.61/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.61/1.98  --bmc1_ucm_relax_model                  4
% 11.61/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.61/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.61/1.98  --bmc1_ucm_layered_model                none
% 11.61/1.98  --bmc1_ucm_max_lemma_size               10
% 11.61/1.98  
% 11.61/1.98  ------ AIG Options
% 11.61/1.98  
% 11.61/1.98  --aig_mode                              false
% 11.61/1.98  
% 11.61/1.98  ------ Instantiation Options
% 11.61/1.98  
% 11.61/1.98  --instantiation_flag                    true
% 11.61/1.98  --inst_sos_flag                         false
% 11.61/1.98  --inst_sos_phase                        true
% 11.61/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.61/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.61/1.98  --inst_lit_sel_side                     num_symb
% 11.61/1.98  --inst_solver_per_active                1400
% 11.61/1.98  --inst_solver_calls_frac                1.
% 11.61/1.98  --inst_passive_queue_type               priority_queues
% 11.61/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.61/1.98  --inst_passive_queues_freq              [25;2]
% 11.61/1.98  --inst_dismatching                      true
% 11.61/1.98  --inst_eager_unprocessed_to_passive     true
% 11.61/1.98  --inst_prop_sim_given                   true
% 11.61/1.98  --inst_prop_sim_new                     false
% 11.61/1.98  --inst_subs_new                         false
% 11.61/1.98  --inst_eq_res_simp                      false
% 11.61/1.98  --inst_subs_given                       false
% 11.61/1.98  --inst_orphan_elimination               true
% 11.61/1.98  --inst_learning_loop_flag               true
% 11.61/1.98  --inst_learning_start                   3000
% 11.61/1.98  --inst_learning_factor                  2
% 11.61/1.98  --inst_start_prop_sim_after_learn       3
% 11.61/1.98  --inst_sel_renew                        solver
% 11.61/1.98  --inst_lit_activity_flag                true
% 11.61/1.98  --inst_restr_to_given                   false
% 11.61/1.98  --inst_activity_threshold               500
% 11.61/1.98  --inst_out_proof                        true
% 11.61/1.98  
% 11.61/1.98  ------ Resolution Options
% 11.61/1.98  
% 11.61/1.98  --resolution_flag                       true
% 11.61/1.98  --res_lit_sel                           adaptive
% 11.61/1.98  --res_lit_sel_side                      none
% 11.61/1.98  --res_ordering                          kbo
% 11.61/1.98  --res_to_prop_solver                    active
% 11.61/1.98  --res_prop_simpl_new                    false
% 11.61/1.98  --res_prop_simpl_given                  true
% 11.61/1.98  --res_passive_queue_type                priority_queues
% 11.61/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.61/1.98  --res_passive_queues_freq               [15;5]
% 11.61/1.98  --res_forward_subs                      full
% 11.61/1.98  --res_backward_subs                     full
% 11.61/1.98  --res_forward_subs_resolution           true
% 11.61/1.98  --res_backward_subs_resolution          true
% 11.61/1.98  --res_orphan_elimination                true
% 11.61/1.98  --res_time_limit                        2.
% 11.61/1.98  --res_out_proof                         true
% 11.61/1.98  
% 11.61/1.98  ------ Superposition Options
% 11.61/1.98  
% 11.61/1.98  --superposition_flag                    true
% 11.61/1.98  --sup_passive_queue_type                priority_queues
% 11.61/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.61/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.61/1.98  --demod_completeness_check              fast
% 11.61/1.98  --demod_use_ground                      true
% 11.61/1.98  --sup_to_prop_solver                    passive
% 11.61/1.98  --sup_prop_simpl_new                    true
% 11.61/1.98  --sup_prop_simpl_given                  true
% 11.61/1.98  --sup_fun_splitting                     false
% 11.61/1.98  --sup_smt_interval                      50000
% 11.61/1.98  
% 11.61/1.98  ------ Superposition Simplification Setup
% 11.61/1.98  
% 11.61/1.98  --sup_indices_passive                   []
% 11.61/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.61/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.98  --sup_full_bw                           [BwDemod]
% 11.61/1.98  --sup_immed_triv                        [TrivRules]
% 11.61/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.61/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.98  --sup_immed_bw_main                     []
% 11.61/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.61/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.61/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.61/1.98  
% 11.61/1.98  ------ Combination Options
% 11.61/1.98  
% 11.61/1.98  --comb_res_mult                         3
% 11.61/1.98  --comb_sup_mult                         2
% 11.61/1.98  --comb_inst_mult                        10
% 11.61/1.98  
% 11.61/1.98  ------ Debug Options
% 11.61/1.98  
% 11.61/1.98  --dbg_backtrace                         false
% 11.61/1.98  --dbg_dump_prop_clauses                 false
% 11.61/1.98  --dbg_dump_prop_clauses_file            -
% 11.61/1.98  --dbg_out_stat                          false
% 11.61/1.98  ------ Parsing...
% 11.61/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.61/1.98  
% 11.61/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.61/1.98  
% 11.61/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.61/1.98  
% 11.61/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.61/1.98  ------ Proving...
% 11.61/1.98  ------ Problem Properties 
% 11.61/1.98  
% 11.61/1.98  
% 11.61/1.98  clauses                                 71
% 11.61/1.98  conjectures                             13
% 11.61/1.98  EPR                                     16
% 11.61/1.98  Horn                                    62
% 11.61/1.98  unary                                   24
% 11.61/1.98  binary                                  21
% 11.61/1.98  lits                                    200
% 11.61/1.98  lits eq                                 21
% 11.61/1.98  fd_pure                                 0
% 11.61/1.98  fd_pseudo                               0
% 11.61/1.98  fd_cond                                 5
% 11.61/1.98  fd_pseudo_cond                          4
% 11.61/1.98  AC symbols                              0
% 11.61/1.98  
% 11.61/1.98  ------ Schedule dynamic 5 is on 
% 11.61/1.98  
% 11.61/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.61/1.98  
% 11.61/1.98  
% 11.61/1.98  ------ 
% 11.61/1.98  Current options:
% 11.61/1.98  ------ 
% 11.61/1.98  
% 11.61/1.98  ------ Input Options
% 11.61/1.98  
% 11.61/1.98  --out_options                           all
% 11.61/1.98  --tptp_safe_out                         true
% 11.61/1.98  --problem_path                          ""
% 11.61/1.98  --include_path                          ""
% 11.61/1.98  --clausifier                            res/vclausify_rel
% 11.61/1.98  --clausifier_options                    --mode clausify
% 11.61/1.98  --stdin                                 false
% 11.61/1.98  --stats_out                             all
% 11.61/1.98  
% 11.61/1.98  ------ General Options
% 11.61/1.98  
% 11.61/1.98  --fof                                   false
% 11.61/1.98  --time_out_real                         305.
% 11.61/1.98  --time_out_virtual                      -1.
% 11.61/1.98  --symbol_type_check                     false
% 11.61/1.98  --clausify_out                          false
% 11.61/1.98  --sig_cnt_out                           false
% 11.61/1.98  --trig_cnt_out                          false
% 11.61/1.98  --trig_cnt_out_tolerance                1.
% 11.61/1.98  --trig_cnt_out_sk_spl                   false
% 11.61/1.98  --abstr_cl_out                          false
% 11.61/1.98  
% 11.61/1.98  ------ Global Options
% 11.61/1.98  
% 11.61/1.98  --schedule                              default
% 11.61/1.98  --add_important_lit                     false
% 11.61/1.98  --prop_solver_per_cl                    1000
% 11.61/1.98  --min_unsat_core                        false
% 11.61/1.98  --soft_assumptions                      false
% 11.61/1.98  --soft_lemma_size                       3
% 11.61/1.98  --prop_impl_unit_size                   0
% 11.61/1.98  --prop_impl_unit                        []
% 11.61/1.98  --share_sel_clauses                     true
% 11.61/1.98  --reset_solvers                         false
% 11.61/1.98  --bc_imp_inh                            [conj_cone]
% 11.61/1.98  --conj_cone_tolerance                   3.
% 11.61/1.98  --extra_neg_conj                        none
% 11.61/1.98  --large_theory_mode                     true
% 11.61/1.98  --prolific_symb_bound                   200
% 11.61/1.98  --lt_threshold                          2000
% 11.61/1.98  --clause_weak_htbl                      true
% 11.61/1.98  --gc_record_bc_elim                     false
% 11.61/1.98  
% 11.61/1.98  ------ Preprocessing Options
% 11.61/1.98  
% 11.61/1.98  --preprocessing_flag                    true
% 11.61/1.98  --time_out_prep_mult                    0.1
% 11.61/1.98  --splitting_mode                        input
% 11.61/1.98  --splitting_grd                         true
% 11.61/1.98  --splitting_cvd                         false
% 11.61/1.98  --splitting_cvd_svl                     false
% 11.61/1.98  --splitting_nvd                         32
% 11.61/1.98  --sub_typing                            true
% 11.61/1.98  --prep_gs_sim                           true
% 11.61/1.98  --prep_unflatten                        true
% 11.61/1.98  --prep_res_sim                          true
% 11.61/1.98  --prep_upred                            true
% 11.61/1.98  --prep_sem_filter                       exhaustive
% 11.61/1.98  --prep_sem_filter_out                   false
% 11.61/1.98  --pred_elim                             true
% 11.61/1.98  --res_sim_input                         true
% 11.61/1.98  --eq_ax_congr_red                       true
% 11.61/1.98  --pure_diseq_elim                       true
% 11.61/1.98  --brand_transform                       false
% 11.61/1.98  --non_eq_to_eq                          false
% 11.61/1.98  --prep_def_merge                        true
% 11.61/1.98  --prep_def_merge_prop_impl              false
% 11.61/1.98  --prep_def_merge_mbd                    true
% 11.61/1.98  --prep_def_merge_tr_red                 false
% 11.61/1.98  --prep_def_merge_tr_cl                  false
% 11.61/1.98  --smt_preprocessing                     true
% 11.61/1.98  --smt_ac_axioms                         fast
% 11.61/1.98  --preprocessed_out                      false
% 11.61/1.98  --preprocessed_stats                    false
% 11.61/1.98  
% 11.61/1.98  ------ Abstraction refinement Options
% 11.61/1.98  
% 11.61/1.98  --abstr_ref                             []
% 11.61/1.98  --abstr_ref_prep                        false
% 11.61/1.98  --abstr_ref_until_sat                   false
% 11.61/1.98  --abstr_ref_sig_restrict                funpre
% 11.61/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.61/1.98  --abstr_ref_under                       []
% 11.61/1.98  
% 11.61/1.98  ------ SAT Options
% 11.61/1.98  
% 11.61/1.98  --sat_mode                              false
% 11.61/1.98  --sat_fm_restart_options                ""
% 11.61/1.98  --sat_gr_def                            false
% 11.61/1.98  --sat_epr_types                         true
% 11.61/1.98  --sat_non_cyclic_types                  false
% 11.61/1.98  --sat_finite_models                     false
% 11.61/1.98  --sat_fm_lemmas                         false
% 11.61/1.98  --sat_fm_prep                           false
% 11.61/1.98  --sat_fm_uc_incr                        true
% 11.61/1.98  --sat_out_model                         small
% 11.61/1.98  --sat_out_clauses                       false
% 11.61/1.98  
% 11.61/1.98  ------ QBF Options
% 11.61/1.98  
% 11.61/1.98  --qbf_mode                              false
% 11.61/1.98  --qbf_elim_univ                         false
% 11.61/1.98  --qbf_dom_inst                          none
% 11.61/1.98  --qbf_dom_pre_inst                      false
% 11.61/1.98  --qbf_sk_in                             false
% 11.61/1.98  --qbf_pred_elim                         true
% 11.61/1.98  --qbf_split                             512
% 11.61/1.98  
% 11.61/1.98  ------ BMC1 Options
% 11.61/1.98  
% 11.61/1.98  --bmc1_incremental                      false
% 11.61/1.98  --bmc1_axioms                           reachable_all
% 11.61/1.98  --bmc1_min_bound                        0
% 11.61/1.98  --bmc1_max_bound                        -1
% 11.61/1.98  --bmc1_max_bound_default                -1
% 11.61/1.98  --bmc1_symbol_reachability              true
% 11.61/1.98  --bmc1_property_lemmas                  false
% 11.61/1.98  --bmc1_k_induction                      false
% 11.61/1.98  --bmc1_non_equiv_states                 false
% 11.61/1.98  --bmc1_deadlock                         false
% 11.61/1.98  --bmc1_ucm                              false
% 11.61/1.98  --bmc1_add_unsat_core                   none
% 11.61/1.98  --bmc1_unsat_core_children              false
% 11.61/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.61/1.98  --bmc1_out_stat                         full
% 11.61/1.98  --bmc1_ground_init                      false
% 11.61/1.98  --bmc1_pre_inst_next_state              false
% 11.61/1.98  --bmc1_pre_inst_state                   false
% 11.61/1.98  --bmc1_pre_inst_reach_state             false
% 11.61/1.98  --bmc1_out_unsat_core                   false
% 11.61/1.98  --bmc1_aig_witness_out                  false
% 11.61/1.98  --bmc1_verbose                          false
% 11.61/1.98  --bmc1_dump_clauses_tptp                false
% 11.61/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.61/1.98  --bmc1_dump_file                        -
% 11.61/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.61/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.61/1.98  --bmc1_ucm_extend_mode                  1
% 11.61/1.98  --bmc1_ucm_init_mode                    2
% 11.61/1.98  --bmc1_ucm_cone_mode                    none
% 11.61/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.61/1.98  --bmc1_ucm_relax_model                  4
% 11.61/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.61/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.61/1.98  --bmc1_ucm_layered_model                none
% 11.61/1.98  --bmc1_ucm_max_lemma_size               10
% 11.61/1.98  
% 11.61/1.98  ------ AIG Options
% 11.61/1.98  
% 11.61/1.98  --aig_mode                              false
% 11.61/1.98  
% 11.61/1.98  ------ Instantiation Options
% 11.61/1.98  
% 11.61/1.98  --instantiation_flag                    true
% 11.61/1.98  --inst_sos_flag                         false
% 11.61/1.98  --inst_sos_phase                        true
% 11.61/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.61/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.61/1.98  --inst_lit_sel_side                     none
% 11.61/1.98  --inst_solver_per_active                1400
% 11.61/1.98  --inst_solver_calls_frac                1.
% 11.61/1.98  --inst_passive_queue_type               priority_queues
% 11.61/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.61/1.98  --inst_passive_queues_freq              [25;2]
% 11.61/1.98  --inst_dismatching                      true
% 11.61/1.98  --inst_eager_unprocessed_to_passive     true
% 11.61/1.98  --inst_prop_sim_given                   true
% 11.61/1.98  --inst_prop_sim_new                     false
% 11.61/1.98  --inst_subs_new                         false
% 11.61/1.98  --inst_eq_res_simp                      false
% 11.61/1.98  --inst_subs_given                       false
% 11.61/1.98  --inst_orphan_elimination               true
% 11.61/1.98  --inst_learning_loop_flag               true
% 11.61/1.98  --inst_learning_start                   3000
% 11.61/1.98  --inst_learning_factor                  2
% 11.61/1.98  --inst_start_prop_sim_after_learn       3
% 11.61/1.98  --inst_sel_renew                        solver
% 11.61/1.98  --inst_lit_activity_flag                true
% 11.61/1.98  --inst_restr_to_given                   false
% 11.61/1.98  --inst_activity_threshold               500
% 11.61/1.98  --inst_out_proof                        true
% 11.61/1.98  
% 11.61/1.98  ------ Resolution Options
% 11.61/1.98  
% 11.61/1.98  --resolution_flag                       false
% 11.61/1.98  --res_lit_sel                           adaptive
% 11.61/1.98  --res_lit_sel_side                      none
% 11.61/1.98  --res_ordering                          kbo
% 11.61/1.98  --res_to_prop_solver                    active
% 11.61/1.98  --res_prop_simpl_new                    false
% 11.61/1.98  --res_prop_simpl_given                  true
% 11.61/1.98  --res_passive_queue_type                priority_queues
% 11.61/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.61/1.98  --res_passive_queues_freq               [15;5]
% 11.61/1.98  --res_forward_subs                      full
% 11.61/1.98  --res_backward_subs                     full
% 11.61/1.98  --res_forward_subs_resolution           true
% 11.61/1.98  --res_backward_subs_resolution          true
% 11.61/1.98  --res_orphan_elimination                true
% 11.61/1.98  --res_time_limit                        2.
% 11.61/1.98  --res_out_proof                         true
% 11.61/1.98  
% 11.61/1.98  ------ Superposition Options
% 11.61/1.98  
% 11.61/1.98  --superposition_flag                    true
% 11.61/1.98  --sup_passive_queue_type                priority_queues
% 11.61/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.61/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.61/1.98  --demod_completeness_check              fast
% 11.61/1.98  --demod_use_ground                      true
% 11.61/1.98  --sup_to_prop_solver                    passive
% 11.61/1.98  --sup_prop_simpl_new                    true
% 11.61/1.98  --sup_prop_simpl_given                  true
% 11.61/1.98  --sup_fun_splitting                     false
% 11.61/1.98  --sup_smt_interval                      50000
% 11.61/1.98  
% 11.61/1.98  ------ Superposition Simplification Setup
% 11.61/1.98  
% 11.61/1.98  --sup_indices_passive                   []
% 11.61/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.61/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.61/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.98  --sup_full_bw                           [BwDemod]
% 11.61/1.98  --sup_immed_triv                        [TrivRules]
% 11.61/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.61/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.98  --sup_immed_bw_main                     []
% 11.61/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.61/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.61/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.61/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.61/1.98  
% 11.61/1.98  ------ Combination Options
% 11.61/1.98  
% 11.61/1.98  --comb_res_mult                         3
% 11.61/1.98  --comb_sup_mult                         2
% 11.61/1.98  --comb_inst_mult                        10
% 11.61/1.98  
% 11.61/1.98  ------ Debug Options
% 11.61/1.98  
% 11.61/1.98  --dbg_backtrace                         false
% 11.61/1.98  --dbg_dump_prop_clauses                 false
% 11.61/1.98  --dbg_dump_prop_clauses_file            -
% 11.61/1.98  --dbg_out_stat                          false
% 11.61/1.98  
% 11.61/1.98  
% 11.61/1.98  
% 11.61/1.98  
% 11.61/1.98  ------ Proving...
% 11.61/1.98  
% 11.61/1.98  
% 11.61/1.98  % SZS status Theorem for theBenchmark.p
% 11.61/1.98  
% 11.61/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.61/1.98  
% 11.61/1.98  fof(f35,conjecture,(
% 11.61/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f36,negated_conjecture,(
% 11.61/1.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 11.61/1.98    inference(negated_conjecture,[],[f35])).
% 11.61/1.98  
% 11.61/1.98  fof(f75,plain,(
% 11.61/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.61/1.98    inference(ennf_transformation,[],[f36])).
% 11.61/1.98  
% 11.61/1.98  fof(f76,plain,(
% 11.61/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.61/1.98    inference(flattening,[],[f75])).
% 11.61/1.98  
% 11.61/1.98  fof(f107,plain,(
% 11.61/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.61/1.98    inference(nnf_transformation,[],[f76])).
% 11.61/1.98  
% 11.61/1.98  fof(f108,plain,(
% 11.61/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.61/1.98    inference(flattening,[],[f107])).
% 11.61/1.98  
% 11.61/1.98  fof(f112,plain,(
% 11.61/1.98    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK9 = X2 & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK9))) )),
% 11.61/1.98    introduced(choice_axiom,[])).
% 11.61/1.98  
% 11.61/1.98  fof(f111,plain,(
% 11.61/1.98    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK8,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK8,X0,X1)) & sK8 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 11.61/1.98    introduced(choice_axiom,[])).
% 11.61/1.98  
% 11.61/1.98  fof(f110,plain,(
% 11.61/1.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(X2,X0,sK7)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(X2,X0,sK7)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7)) & v1_funct_1(X2)) & l1_pre_topc(sK7) & v2_pre_topc(sK7))) )),
% 11.61/1.98    introduced(choice_axiom,[])).
% 11.61/1.98  
% 11.61/1.98  fof(f109,plain,(
% 11.61/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK6,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK6,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 11.61/1.98    introduced(choice_axiom,[])).
% 11.61/1.98  
% 11.61/1.98  fof(f113,plain,(
% 11.61/1.98    ((((~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(sK8,sK6,sK7)) & (v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,sK7)) & sK8 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) & v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) & v1_funct_1(sK9)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) & v1_funct_1(sK8)) & l1_pre_topc(sK7) & v2_pre_topc(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 11.61/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f108,f112,f111,f110,f109])).
% 11.61/1.98  
% 11.61/1.98  fof(f188,plain,(
% 11.61/1.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f192,plain,(
% 11.61/1.98    sK8 = sK9),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f23,axiom,(
% 11.61/1.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f55,plain,(
% 11.61/1.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 11.61/1.98    inference(ennf_transformation,[],[f23])).
% 11.61/1.98  
% 11.61/1.98  fof(f56,plain,(
% 11.61/1.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 11.61/1.98    inference(flattening,[],[f55])).
% 11.61/1.98  
% 11.61/1.98  fof(f155,plain,(
% 11.61/1.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f56])).
% 11.61/1.98  
% 11.61/1.98  fof(f24,axiom,(
% 11.61/1.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f57,plain,(
% 11.61/1.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.61/1.98    inference(ennf_transformation,[],[f24])).
% 11.61/1.98  
% 11.61/1.98  fof(f58,plain,(
% 11.61/1.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.61/1.98    inference(flattening,[],[f57])).
% 11.61/1.98  
% 11.61/1.98  fof(f98,plain,(
% 11.61/1.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.61/1.98    inference(nnf_transformation,[],[f58])).
% 11.61/1.98  
% 11.61/1.98  fof(f156,plain,(
% 11.61/1.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f98])).
% 11.61/1.98  
% 11.61/1.98  fof(f18,axiom,(
% 11.61/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f49,plain,(
% 11.61/1.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.61/1.98    inference(ennf_transformation,[],[f18])).
% 11.61/1.98  
% 11.61/1.98  fof(f145,plain,(
% 11.61/1.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.61/1.98    inference(cnf_transformation,[],[f49])).
% 11.61/1.98  
% 11.61/1.98  fof(f17,axiom,(
% 11.61/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f48,plain,(
% 11.61/1.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.61/1.98    inference(ennf_transformation,[],[f17])).
% 11.61/1.98  
% 11.61/1.98  fof(f144,plain,(
% 11.61/1.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.61/1.98    inference(cnf_transformation,[],[f48])).
% 11.61/1.98  
% 11.61/1.98  fof(f189,plain,(
% 11.61/1.98    v1_funct_1(sK9)),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f187,plain,(
% 11.61/1.98    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f4,axiom,(
% 11.61/1.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f40,plain,(
% 11.61/1.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 11.61/1.98    inference(ennf_transformation,[],[f4])).
% 11.61/1.98  
% 11.61/1.98  fof(f120,plain,(
% 11.61/1.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f40])).
% 11.61/1.98  
% 11.61/1.98  fof(f191,plain,(
% 11.61/1.98    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f190,plain,(
% 11.61/1.98    v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f21,axiom,(
% 11.61/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f53,plain,(
% 11.61/1.98    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.61/1.98    inference(ennf_transformation,[],[f21])).
% 11.61/1.98  
% 11.61/1.98  fof(f150,plain,(
% 11.61/1.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.61/1.98    inference(cnf_transformation,[],[f53])).
% 11.61/1.98  
% 11.61/1.98  fof(f16,axiom,(
% 11.61/1.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f142,plain,(
% 11.61/1.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.61/1.98    inference(cnf_transformation,[],[f16])).
% 11.61/1.98  
% 11.61/1.98  fof(f27,axiom,(
% 11.61/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f61,plain,(
% 11.61/1.98    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.61/1.98    inference(ennf_transformation,[],[f27])).
% 11.61/1.98  
% 11.61/1.98  fof(f62,plain,(
% 11.61/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.61/1.98    inference(flattening,[],[f61])).
% 11.61/1.98  
% 11.61/1.98  fof(f168,plain,(
% 11.61/1.98    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f62])).
% 11.61/1.98  
% 11.61/1.98  fof(f11,axiom,(
% 11.61/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f93,plain,(
% 11.61/1.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.61/1.98    inference(nnf_transformation,[],[f11])).
% 11.61/1.98  
% 11.61/1.98  fof(f134,plain,(
% 11.61/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.61/1.98    inference(cnf_transformation,[],[f93])).
% 11.61/1.98  
% 11.61/1.98  fof(f5,axiom,(
% 11.61/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f85,plain,(
% 11.61/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.61/1.98    inference(nnf_transformation,[],[f5])).
% 11.61/1.98  
% 11.61/1.98  fof(f86,plain,(
% 11.61/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.61/1.98    inference(flattening,[],[f85])).
% 11.61/1.98  
% 11.61/1.98  fof(f123,plain,(
% 11.61/1.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f86])).
% 11.61/1.98  
% 11.61/1.98  fof(f8,axiom,(
% 11.61/1.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f91,plain,(
% 11.61/1.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.61/1.98    inference(nnf_transformation,[],[f8])).
% 11.61/1.98  
% 11.61/1.98  fof(f92,plain,(
% 11.61/1.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.61/1.98    inference(flattening,[],[f91])).
% 11.61/1.98  
% 11.61/1.98  fof(f131,plain,(
% 11.61/1.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.61/1.98    inference(cnf_transformation,[],[f92])).
% 11.61/1.98  
% 11.61/1.98  fof(f199,plain,(
% 11.61/1.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.61/1.98    inference(equality_resolution,[],[f131])).
% 11.61/1.98  
% 11.61/1.98  fof(f143,plain,(
% 11.61/1.98    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 11.61/1.98    inference(cnf_transformation,[],[f16])).
% 11.61/1.98  
% 11.61/1.98  fof(f26,axiom,(
% 11.61/1.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f59,plain,(
% 11.61/1.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.61/1.98    inference(ennf_transformation,[],[f26])).
% 11.61/1.98  
% 11.61/1.98  fof(f60,plain,(
% 11.61/1.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.61/1.98    inference(flattening,[],[f59])).
% 11.61/1.98  
% 11.61/1.98  fof(f166,plain,(
% 11.61/1.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f60])).
% 11.61/1.98  
% 11.61/1.98  fof(f130,plain,(
% 11.61/1.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.61/1.98    inference(cnf_transformation,[],[f92])).
% 11.61/1.98  
% 11.61/1.98  fof(f200,plain,(
% 11.61/1.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.61/1.98    inference(equality_resolution,[],[f130])).
% 11.61/1.98  
% 11.61/1.98  fof(f135,plain,(
% 11.61/1.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f93])).
% 11.61/1.98  
% 11.61/1.98  fof(f121,plain,(
% 11.61/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.61/1.98    inference(cnf_transformation,[],[f86])).
% 11.61/1.98  
% 11.61/1.98  fof(f196,plain,(
% 11.61/1.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.61/1.98    inference(equality_resolution,[],[f121])).
% 11.61/1.98  
% 11.61/1.98  fof(f13,axiom,(
% 11.61/1.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f45,plain,(
% 11.61/1.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.61/1.98    inference(ennf_transformation,[],[f13])).
% 11.61/1.98  
% 11.61/1.98  fof(f94,plain,(
% 11.61/1.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.61/1.98    inference(nnf_transformation,[],[f45])).
% 11.61/1.98  
% 11.61/1.98  fof(f137,plain,(
% 11.61/1.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f94])).
% 11.61/1.98  
% 11.61/1.98  fof(f193,plain,(
% 11.61/1.98    v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | v5_pre_topc(sK8,sK6,sK7)),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f20,axiom,(
% 11.61/1.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f51,plain,(
% 11.61/1.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 11.61/1.98    inference(ennf_transformation,[],[f20])).
% 11.61/1.98  
% 11.61/1.98  fof(f52,plain,(
% 11.61/1.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 11.61/1.98    inference(flattening,[],[f51])).
% 11.61/1.98  
% 11.61/1.98  fof(f148,plain,(
% 11.61/1.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 11.61/1.98    inference(cnf_transformation,[],[f52])).
% 11.61/1.98  
% 11.61/1.98  fof(f34,axiom,(
% 11.61/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f73,plain,(
% 11.61/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.61/1.98    inference(ennf_transformation,[],[f34])).
% 11.61/1.98  
% 11.61/1.98  fof(f74,plain,(
% 11.61/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.61/1.98    inference(flattening,[],[f73])).
% 11.61/1.98  
% 11.61/1.98  fof(f106,plain,(
% 11.61/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.61/1.98    inference(nnf_transformation,[],[f74])).
% 11.61/1.98  
% 11.61/1.98  fof(f181,plain,(
% 11.61/1.98    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f106])).
% 11.61/1.98  
% 11.61/1.98  fof(f204,plain,(
% 11.61/1.98    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.61/1.98    inference(equality_resolution,[],[f181])).
% 11.61/1.98  
% 11.61/1.98  fof(f184,plain,(
% 11.61/1.98    v2_pre_topc(sK7)),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f185,plain,(
% 11.61/1.98    l1_pre_topc(sK7)),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f182,plain,(
% 11.61/1.98    v2_pre_topc(sK6)),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f183,plain,(
% 11.61/1.98    l1_pre_topc(sK6)),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f31,axiom,(
% 11.61/1.98    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f68,plain,(
% 11.61/1.98    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.61/1.98    inference(ennf_transformation,[],[f31])).
% 11.61/1.98  
% 11.61/1.98  fof(f176,plain,(
% 11.61/1.98    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f68])).
% 11.61/1.98  
% 11.61/1.98  fof(f32,axiom,(
% 11.61/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f38,plain,(
% 11.61/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 11.61/1.98    inference(pure_predicate_removal,[],[f32])).
% 11.61/1.98  
% 11.61/1.98  fof(f69,plain,(
% 11.61/1.98    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.61/1.98    inference(ennf_transformation,[],[f38])).
% 11.61/1.98  
% 11.61/1.98  fof(f70,plain,(
% 11.61/1.98    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.61/1.98    inference(flattening,[],[f69])).
% 11.61/1.98  
% 11.61/1.98  fof(f177,plain,(
% 11.61/1.98    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f70])).
% 11.61/1.98  
% 11.61/1.98  fof(f30,axiom,(
% 11.61/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f37,plain,(
% 11.61/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 11.61/1.98    inference(pure_predicate_removal,[],[f30])).
% 11.61/1.98  
% 11.61/1.98  fof(f67,plain,(
% 11.61/1.98    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.61/1.98    inference(ennf_transformation,[],[f37])).
% 11.61/1.98  
% 11.61/1.98  fof(f175,plain,(
% 11.61/1.98    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.61/1.98    inference(cnf_transformation,[],[f67])).
% 11.61/1.98  
% 11.61/1.98  fof(f33,axiom,(
% 11.61/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f71,plain,(
% 11.61/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.61/1.98    inference(ennf_transformation,[],[f33])).
% 11.61/1.98  
% 11.61/1.98  fof(f72,plain,(
% 11.61/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.61/1.98    inference(flattening,[],[f71])).
% 11.61/1.98  
% 11.61/1.98  fof(f105,plain,(
% 11.61/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.61/1.98    inference(nnf_transformation,[],[f72])).
% 11.61/1.98  
% 11.61/1.98  fof(f179,plain,(
% 11.61/1.98    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f105])).
% 11.61/1.98  
% 11.61/1.98  fof(f202,plain,(
% 11.61/1.98    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.61/1.98    inference(equality_resolution,[],[f179])).
% 11.61/1.98  
% 11.61/1.98  fof(f180,plain,(
% 11.61/1.98    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f106])).
% 11.61/1.98  
% 11.61/1.98  fof(f205,plain,(
% 11.61/1.98    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.61/1.98    inference(equality_resolution,[],[f180])).
% 11.61/1.98  
% 11.61/1.98  fof(f194,plain,(
% 11.61/1.98    ~v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) | ~v5_pre_topc(sK8,sK6,sK7)),
% 11.61/1.98    inference(cnf_transformation,[],[f113])).
% 11.61/1.98  
% 11.61/1.98  fof(f178,plain,(
% 11.61/1.98    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f105])).
% 11.61/1.98  
% 11.61/1.98  fof(f203,plain,(
% 11.61/1.98    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.61/1.98    inference(equality_resolution,[],[f178])).
% 11.61/1.98  
% 11.61/1.98  fof(f146,plain,(
% 11.61/1.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.61/1.98    inference(cnf_transformation,[],[f49])).
% 11.61/1.98  
% 11.61/1.98  fof(f14,axiom,(
% 11.61/1.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f46,plain,(
% 11.61/1.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.61/1.98    inference(ennf_transformation,[],[f14])).
% 11.61/1.98  
% 11.61/1.98  fof(f95,plain,(
% 11.61/1.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.61/1.98    inference(nnf_transformation,[],[f46])).
% 11.61/1.98  
% 11.61/1.98  fof(f139,plain,(
% 11.61/1.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f95])).
% 11.61/1.98  
% 11.61/1.98  fof(f25,axiom,(
% 11.61/1.98    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f99,plain,(
% 11.61/1.98    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK4(X0,X1),X0,X1) & v1_funct_1(sK4(X0,X1)) & v5_relat_1(sK4(X0,X1),X1) & v4_relat_1(sK4(X0,X1),X0) & v1_relat_1(sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.61/1.98    introduced(choice_axiom,[])).
% 11.61/1.98  
% 11.61/1.98  fof(f100,plain,(
% 11.61/1.98    ! [X0,X1] : (v1_funct_2(sK4(X0,X1),X0,X1) & v1_funct_1(sK4(X0,X1)) & v5_relat_1(sK4(X0,X1),X1) & v4_relat_1(sK4(X0,X1),X0) & v1_relat_1(sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.61/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f99])).
% 11.61/1.98  
% 11.61/1.98  fof(f162,plain,(
% 11.61/1.98    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 11.61/1.98    inference(cnf_transformation,[],[f100])).
% 11.61/1.98  
% 11.61/1.98  fof(f3,axiom,(
% 11.61/1.98    v1_xboole_0(k1_xboole_0)),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f119,plain,(
% 11.61/1.98    v1_xboole_0(k1_xboole_0)),
% 11.61/1.98    inference(cnf_transformation,[],[f3])).
% 11.61/1.98  
% 11.61/1.98  fof(f158,plain,(
% 11.61/1.98    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.61/1.98    inference(cnf_transformation,[],[f100])).
% 11.61/1.98  
% 11.61/1.98  fof(f10,axiom,(
% 11.61/1.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 11.61/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.61/1.98  
% 11.61/1.98  fof(f43,plain,(
% 11.61/1.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 11.61/1.98    inference(ennf_transformation,[],[f10])).
% 11.61/1.98  
% 11.61/1.98  fof(f133,plain,(
% 11.61/1.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 11.61/1.98    inference(cnf_transformation,[],[f43])).
% 11.61/1.98  
% 11.61/1.98  cnf(c_74,negated_conjecture,
% 11.61/1.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
% 11.61/1.98      inference(cnf_transformation,[],[f188]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5643,plain,
% 11.61/1.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_74]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_70,negated_conjecture,
% 11.61/1.98      ( sK8 = sK9 ),
% 11.61/1.98      inference(cnf_transformation,[],[f192]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5739,plain,
% 11.61/1.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 11.61/1.98      inference(light_normalisation,[status(thm)],[c_5643,c_70]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_40,plain,
% 11.61/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.61/1.98      | v1_partfun1(X0,X1)
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | ~ v1_funct_1(X0)
% 11.61/1.98      | v1_xboole_0(X2) ),
% 11.61/1.98      inference(cnf_transformation,[],[f155]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_43,plain,
% 11.61/1.98      ( ~ v1_partfun1(X0,X1)
% 11.61/1.98      | ~ v4_relat_1(X0,X1)
% 11.61/1.98      | ~ v1_relat_1(X0)
% 11.61/1.98      | k1_relat_1(X0) = X1 ),
% 11.61/1.98      inference(cnf_transformation,[],[f156]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_986,plain,
% 11.61/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.61/1.98      | ~ v4_relat_1(X0,X1)
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | ~ v1_funct_1(X0)
% 11.61/1.98      | ~ v1_relat_1(X0)
% 11.61/1.98      | v1_xboole_0(X2)
% 11.61/1.98      | k1_relat_1(X0) = X1 ),
% 11.61/1.98      inference(resolution,[status(thm)],[c_40,c_43]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_32,plain,
% 11.61/1.98      ( v4_relat_1(X0,X1)
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.61/1.98      inference(cnf_transformation,[],[f145]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_30,plain,
% 11.61/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | v1_relat_1(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f144]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_988,plain,
% 11.61/1.98      ( ~ v1_funct_1(X0)
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | ~ v1_funct_2(X0,X1,X2)
% 11.61/1.98      | v1_xboole_0(X2)
% 11.61/1.98      | k1_relat_1(X0) = X1 ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_986,c_32,c_30]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_989,plain,
% 11.61/1.98      ( ~ v1_funct_2(X0,X1,X2)
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | ~ v1_funct_1(X0)
% 11.61/1.98      | v1_xboole_0(X2)
% 11.61/1.98      | k1_relat_1(X0) = X1 ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_988]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5632,plain,
% 11.61/1.98      ( k1_relat_1(X0) = X1
% 11.61/1.98      | v1_funct_2(X0,X1,X2) != iProver_top
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.61/1.98      | v1_funct_1(X0) != iProver_top
% 11.61/1.98      | v1_xboole_0(X2) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_989]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6821,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_1(sK9) != iProver_top
% 11.61/1.98      | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5739,c_5632]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_73,negated_conjecture,
% 11.61/1.98      ( v1_funct_1(sK9) ),
% 11.61/1.98      inference(cnf_transformation,[],[f189]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_88,plain,
% 11.61/1.98      ( v1_funct_1(sK9) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_75,negated_conjecture,
% 11.61/1.98      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
% 11.61/1.98      inference(cnf_transformation,[],[f187]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5642,plain,
% 11.61/1.98      ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_75]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5730,plain,
% 11.61/1.98      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 11.61/1.98      inference(light_normalisation,[status(thm)],[c_5642,c_70]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_7151,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_6821,c_88,c_5730]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6,plain,
% 11.61/1.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 11.61/1.98      inference(cnf_transformation,[],[f120]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5688,plain,
% 11.61/1.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8037,plain,
% 11.61/1.98      ( u1_struct_0(sK7) = k1_xboole_0
% 11.61/1.98      | u1_struct_0(sK6) = k1_relat_1(sK9) ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_7151,c_5688]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_71,negated_conjecture,
% 11.61/1.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) ),
% 11.61/1.98      inference(cnf_transformation,[],[f191]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5646,plain,
% 11.61/1.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6820,plain,
% 11.61/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_1(sK9) != iProver_top
% 11.61/1.98      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5646,c_5632]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_72,negated_conjecture,
% 11.61/1.98      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
% 11.61/1.98      inference(cnf_transformation,[],[f190]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_89,plain,
% 11.61/1.98      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_7248,plain,
% 11.61/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 11.61/1.98      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_6820,c_88,c_89]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8036,plain,
% 11.61/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_7248,c_5688]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8737,plain,
% 11.61/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 11.61/1.98      | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.98      | u1_struct_0(sK6) = k1_relat_1(sK9) ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8037,c_8036]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8094,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))))) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8037,c_5646]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_35,plain,
% 11.61/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f150]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5673,plain,
% 11.61/1.98      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 11.61/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_16391,plain,
% 11.61/1.98      ( k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),sK9,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),sK9)
% 11.61/1.98      | u1_struct_0(sK6) = k1_relat_1(sK9) ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8094,c_5673]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_28254,plain,
% 11.61/1.98      ( k8_relset_1(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),sK9,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),sK9)
% 11.61/1.98      | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.98      | u1_struct_0(sK6) = k1_relat_1(sK9) ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8737,c_16391]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_29,plain,
% 11.61/1.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.61/1.98      inference(cnf_transformation,[],[f142]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_54,plain,
% 11.61/1.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 11.61/1.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 11.61/1.98      | ~ v1_funct_1(X0)
% 11.61/1.98      | ~ v1_relat_1(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f168]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5661,plain,
% 11.61/1.98      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 11.61/1.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.61/1.98      | v1_funct_1(X0) != iProver_top
% 11.61/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_21,plain,
% 11.61/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.61/1.98      inference(cnf_transformation,[],[f134]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5678,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.61/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9382,plain,
% 11.61/1.98      ( r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5646,c_5678]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_7,plain,
% 11.61/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.61/1.98      inference(cnf_transformation,[],[f123]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5687,plain,
% 11.61/1.98      ( X0 = X1
% 11.61/1.98      | r1_tarski(X1,X0) != iProver_top
% 11.61/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_13102,plain,
% 11.61/1.98      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = sK9
% 11.61/1.98      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))),sK9) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_9382,c_5687]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_15831,plain,
% 11.61/1.98      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = sK9
% 11.61/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 11.61/1.98      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),sK9) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8036,c_13102]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_15,plain,
% 11.61/1.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.61/1.98      inference(cnf_transformation,[],[f199]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_15842,plain,
% 11.61/1.98      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = sK9
% 11.61/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 11.61/1.98      | r1_tarski(k1_xboole_0,sK9) != iProver_top ),
% 11.61/1.98      inference(demodulation,[status(thm)],[c_15831,c_15]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_28,plain,
% 11.61/1.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.61/1.98      inference(cnf_transformation,[],[f143]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_50,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 11.61/1.98      | ~ v1_funct_1(X0)
% 11.61/1.98      | ~ v1_relat_1(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f166]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5664,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 11.61/1.98      | v1_funct_1(X0) != iProver_top
% 11.61/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_18557,plain,
% 11.61/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) = iProver_top
% 11.61/1.98      | v1_funct_1(k1_xboole_0) != iProver_top
% 11.61/1.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_28,c_5664]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_18599,plain,
% 11.61/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 11.61/1.98      | v1_funct_1(k1_xboole_0) != iProver_top
% 11.61/1.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.61/1.98      inference(light_normalisation,[status(thm)],[c_18557,c_29]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_16,plain,
% 11.61/1.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.61/1.98      inference(cnf_transformation,[],[f200]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_18600,plain,
% 11.61/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.61/1.98      | v1_funct_1(k1_xboole_0) != iProver_top
% 11.61/1.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.61/1.98      inference(demodulation,[status(thm)],[c_18599,c_16]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_20,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.61/1.98      inference(cnf_transformation,[],[f135]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_218,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.61/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_220,plain,
% 11.61/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.61/1.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_218]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9,plain,
% 11.61/1.98      ( r1_tarski(X0,X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f196]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_240,plain,
% 11.61/1.98      ( r1_tarski(X0,X0) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_242,plain,
% 11.61/1.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_240]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_18836,plain,
% 11.61/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_18600,c_220,c_242]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_24,plain,
% 11.61/1.98      ( ~ v4_relat_1(X0,X1)
% 11.61/1.98      | r1_tarski(k1_relat_1(X0),X1)
% 11.61/1.98      | ~ v1_relat_1(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f137]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_1016,plain,
% 11.61/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | r1_tarski(k1_relat_1(X0),X1)
% 11.61/1.98      | ~ v1_relat_1(X0) ),
% 11.61/1.98      inference(resolution,[status(thm)],[c_32,c_24]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_1020,plain,
% 11.61/1.98      ( r1_tarski(k1_relat_1(X0),X1)
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_1016,c_30]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_1021,plain,
% 11.61/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_1020]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5631,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_1021]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6414,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_15,c_5631]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_18843,plain,
% 11.61/1.98      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_18836,c_6414]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_18870,plain,
% 11.61/1.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.61/1.98      inference(light_normalisation,[status(thm)],[c_18843,c_29]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_23791,plain,
% 11.61/1.98      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = sK9
% 11.61/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
% 11.61/1.98      inference(forward_subsumption_resolution,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_15842,c_18870]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_23792,plain,
% 11.61/1.98      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0) = sK9
% 11.61/1.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9) ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8036,c_23791]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_24028,plain,
% 11.61/1.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 11.61/1.98      | sK9 = k1_xboole_0 ),
% 11.61/1.98      inference(demodulation,[status(thm)],[c_23792,c_15]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_69,negated_conjecture,
% 11.61/1.98      ( v5_pre_topc(sK8,sK6,sK7)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
% 11.61/1.98      inference(cnf_transformation,[],[f193]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5647,plain,
% 11.61/1.98      ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5886,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top ),
% 11.61/1.98      inference(light_normalisation,[status(thm)],[c_5647,c_70]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5645,plain,
% 11.61/1.98      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_34,plain,
% 11.61/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.61/1.98      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 11.61/1.98      inference(cnf_transformation,[],[f148]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5674,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_21966,plain,
% 11.61/1.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),X0) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5646,c_5674]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_66,plain,
% 11.61/1.98      ( v5_pre_topc(X0,X1,X2)
% 11.61/1.98      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 11.61/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.61/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 11.61/1.98      | ~ v2_pre_topc(X1)
% 11.61/1.98      | ~ v2_pre_topc(X2)
% 11.61/1.98      | ~ l1_pre_topc(X1)
% 11.61/1.98      | ~ l1_pre_topc(X2)
% 11.61/1.98      | ~ v1_funct_1(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f204]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5650,plain,
% 11.61/1.98      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 11.61/1.98      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) != iProver_top
% 11.61/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.61/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 11.61/1.98      | v2_pre_topc(X1) != iProver_top
% 11.61/1.98      | v2_pre_topc(X2) != iProver_top
% 11.61/1.98      | l1_pre_topc(X1) != iProver_top
% 11.61/1.98      | l1_pre_topc(X2) != iProver_top
% 11.61/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_66]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_23071,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,X0,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,X0,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(X0)) != iProver_top
% 11.61/1.98      | v2_pre_topc(X0) != iProver_top
% 11.61/1.98      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.98      | l1_pre_topc(X0) != iProver_top
% 11.61/1.98      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.98      | v1_funct_1(sK9) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_21966,c_5650]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_78,negated_conjecture,
% 11.61/1.98      ( v2_pre_topc(sK7) ),
% 11.61/1.98      inference(cnf_transformation,[],[f184]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_83,plain,
% 11.61/1.98      ( v2_pre_topc(sK7) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_78]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_77,negated_conjecture,
% 11.61/1.98      ( l1_pre_topc(sK7) ),
% 11.61/1.98      inference(cnf_transformation,[],[f185]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_84,plain,
% 11.61/1.98      ( l1_pre_topc(sK7) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_77]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_27513,plain,
% 11.61/1.98      ( v2_pre_topc(X0) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(X0)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,X0,sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,X0,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_23071,c_83,c_84,c_88]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_27514,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,X0,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,X0,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(X0)) != iProver_top
% 11.61/1.98      | v2_pre_topc(X0) != iProver_top
% 11.61/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_27513]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_21967,plain,
% 11.61/1.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK7)))) = iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),X0) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5739,c_5674]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_27527,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,X0,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,X0,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(X0)) != iProver_top
% 11.61/1.98      | v2_pre_topc(X0) != iProver_top
% 11.61/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.61/1.98      inference(forward_subsumption_resolution,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_27514,c_21967]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_27531,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 11.61/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5645,c_27527]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_80,negated_conjecture,
% 11.61/1.98      ( v2_pre_topc(sK6) ),
% 11.61/1.98      inference(cnf_transformation,[],[f182]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_81,plain,
% 11.61/1.98      ( v2_pre_topc(sK6) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_80]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_79,negated_conjecture,
% 11.61/1.98      ( l1_pre_topc(sK6) ),
% 11.61/1.98      inference(cnf_transformation,[],[f183]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_82,plain,
% 11.61/1.98      ( l1_pre_topc(sK6) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_79]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_90,plain,
% 11.61/1.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_62,plain,
% 11.61/1.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 11.61/1.98      | ~ l1_pre_topc(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f176]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6248,plain,
% 11.61/1.98      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
% 11.61/1.98      | ~ l1_pre_topc(sK6) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_62]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6249,plain,
% 11.61/1.98      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
% 11.61/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_6248]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_63,plain,
% 11.61/1.98      ( ~ v2_pre_topc(X0)
% 11.61/1.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 11.61/1.98      | ~ l1_pre_topc(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f177]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6275,plain,
% 11.61/1.98      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))
% 11.61/1.98      | ~ v2_pre_topc(sK6)
% 11.61/1.98      | ~ l1_pre_topc(sK6) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_63]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6276,plain,
% 11.61/1.98      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top
% 11.61/1.98      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_6275]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6350,plain,
% 11.61/1.98      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_1021]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6351,plain,
% 11.61/1.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_6350]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_61,plain,
% 11.61/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.61/1.98      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 11.61/1.98      inference(cnf_transformation,[],[f175]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6640,plain,
% 11.61/1.98      ( ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
% 11.61/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_61]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6641,plain,
% 11.61/1.98      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top
% 11.61/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_6640]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_27639,plain,
% 11.61/1.98      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_27531,c_81,c_82,c_90,c_6249,c_6276,c_6351,c_6641]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_27640,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_27639]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_27649,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5886,c_27640]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_27816,plain,
% 11.61/1.98      ( sK9 = k1_xboole_0
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_24028,c_27649]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_64,plain,
% 11.61/1.98      ( v5_pre_topc(X0,X1,X2)
% 11.61/1.98      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 11.61/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.61/1.98      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 11.61/1.98      | ~ v2_pre_topc(X1)
% 11.61/1.98      | ~ v2_pre_topc(X2)
% 11.61/1.98      | ~ l1_pre_topc(X1)
% 11.61/1.98      | ~ l1_pre_topc(X2)
% 11.61/1.98      | ~ v1_funct_1(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f202]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5652,plain,
% 11.61/1.98      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 11.61/1.98      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 11.61/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.61/1.98      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(X1) != iProver_top
% 11.61/1.98      | v2_pre_topc(X2) != iProver_top
% 11.61/1.98      | l1_pre_topc(X1) != iProver_top
% 11.61/1.98      | l1_pre_topc(X2) != iProver_top
% 11.61/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_22726,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,X0,sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(X0) != iProver_top
% 11.61/1.98      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.98      | l1_pre_topc(X0) != iProver_top
% 11.61/1.98      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.98      | v1_funct_1(sK9) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_21967,c_5652]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_28059,plain,
% 11.61/1.98      ( v2_pre_topc(X0) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,X0,sK7) = iProver_top
% 11.61/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_22726,c_83,c_84,c_88]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_28060,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,X0,sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(X0) != iProver_top
% 11.61/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_28059]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_28073,plain,
% 11.61/1.98      ( sK9 = k1_xboole_0
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_24028,c_28060]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_32039,plain,
% 11.61/1.98      ( sK9 = k1_xboole_0
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_27816,c_81,c_82,c_90,c_5730,c_5739,c_6351,c_28073]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_67,plain,
% 11.61/1.98      ( ~ v5_pre_topc(X0,X1,X2)
% 11.61/1.98      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 11.61/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.61/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 11.61/1.98      | ~ v2_pre_topc(X1)
% 11.61/1.98      | ~ v2_pre_topc(X2)
% 11.61/1.98      | ~ l1_pre_topc(X1)
% 11.61/1.98      | ~ l1_pre_topc(X2)
% 11.61/1.98      | ~ v1_funct_1(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f205]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5649,plain,
% 11.61/1.98      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 11.61/1.98      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 11.61/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.61/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 11.61/1.98      | v2_pre_topc(X1) != iProver_top
% 11.61/1.98      | v2_pre_topc(X2) != iProver_top
% 11.61/1.98      | l1_pre_topc(X1) != iProver_top
% 11.61/1.98      | l1_pre_topc(X2) != iProver_top
% 11.61/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8527,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 11.61/1.98      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 11.61/1.98      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.98      | v1_funct_1(sK9) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5646,c_5649]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8696,plain,
% 11.61/1.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_8527,c_81,c_82,c_83,c_84,c_88,c_89,c_6249,c_6276,
% 11.61/1.98                 c_6641]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8697,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_8696]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8704,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0))) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8037,c_8697]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8705,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.61/1.98      inference(demodulation,[status(thm)],[c_8704,c_15]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_22733,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_21967,c_8697]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_25617,plain,
% 11.61/1.98      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_8705,c_90,c_6351,c_22733]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_25618,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_25617]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_68,negated_conjecture,
% 11.61/1.98      ( ~ v5_pre_topc(sK8,sK6,sK7)
% 11.61/1.98      | ~ v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
% 11.61/1.98      inference(cnf_transformation,[],[f194]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5648,plain,
% 11.61/1.98      ( v5_pre_topc(sK8,sK6,sK7) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5903,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) != iProver_top ),
% 11.61/1.98      inference(light_normalisation,[status(thm)],[c_5648,c_70]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_25627,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_25618,c_5903]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_25659,plain,
% 11.61/1.98      ( sK9 = k1_xboole_0
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_24028,c_25627]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_65,plain,
% 11.61/1.98      ( ~ v5_pre_topc(X0,X1,X2)
% 11.61/1.98      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 11.61/1.98      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.61/1.98      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 11.61/1.98      | ~ v2_pre_topc(X1)
% 11.61/1.98      | ~ v2_pre_topc(X2)
% 11.61/1.98      | ~ l1_pre_topc(X1)
% 11.61/1.98      | ~ l1_pre_topc(X2)
% 11.61/1.98      | ~ v1_funct_1(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f203]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5651,plain,
% 11.61/1.98      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 11.61/1.98      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 11.61/1.98      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 11.61/1.98      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 11.61/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(X1) != iProver_top
% 11.61/1.98      | v2_pre_topc(X2) != iProver_top
% 11.61/1.98      | l1_pre_topc(X1) != iProver_top
% 11.61/1.98      | l1_pre_topc(X2) != iProver_top
% 11.61/1.98      | v1_funct_1(X0) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_22727,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,X0,sK7) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(X0) != iProver_top
% 11.61/1.98      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.98      | l1_pre_topc(X0) != iProver_top
% 11.61/1.98      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.98      | v1_funct_1(sK9) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_21967,c_5651]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_29612,plain,
% 11.61/1.98      ( v2_pre_topc(X0) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,X0,sK7) != iProver_top
% 11.61/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_22727,c_83,c_84,c_88]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_29613,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,X0,sK7) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(X0) != iProver_top
% 11.61/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_29612]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_29627,plain,
% 11.61/1.98      ( sK9 = k1_xboole_0
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.98      | l1_pre_topc(sK6) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_24028,c_29613]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_32043,plain,
% 11.61/1.98      ( sK9 = k1_xboole_0
% 11.61/1.98      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_32039,c_81,c_82,c_90,c_5730,c_5739,c_6351,c_25659,
% 11.61/1.98                 c_29627]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_32049,plain,
% 11.61/1.98      ( sK9 = k1_xboole_0
% 11.61/1.98      | r1_tarski(k2_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v1_funct_1(sK9) != iProver_top
% 11.61/1.98      | v1_relat_1(sK9) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5661,c_32043]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6260,plain,
% 11.61/1.98      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 11.61/1.98      | v1_relat_1(sK9) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_30]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6261,plain,
% 11.61/1.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.98      | v1_relat_1(sK9) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_6260]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_31,plain,
% 11.61/1.98      ( v5_relat_1(X0,X1)
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.61/1.98      inference(cnf_transformation,[],[f146]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_26,plain,
% 11.61/1.98      ( ~ v5_relat_1(X0,X1)
% 11.61/1.98      | r1_tarski(k2_relat_1(X0),X1)
% 11.61/1.98      | ~ v1_relat_1(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f139]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_948,plain,
% 11.61/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | r1_tarski(k2_relat_1(X0),X2)
% 11.61/1.98      | ~ v1_relat_1(X0) ),
% 11.61/1.98      inference(resolution,[status(thm)],[c_31,c_26]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_952,plain,
% 11.61/1.98      ( r1_tarski(k2_relat_1(X0),X2)
% 11.61/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_948,c_30]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_953,plain,
% 11.61/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.61/1.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_952]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5634,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.61/1.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_953]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8144,plain,
% 11.61/1.98      ( r1_tarski(k2_relat_1(sK9),u1_struct_0(sK7)) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5739,c_5634]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_38544,plain,
% 11.61/1.98      ( sK9 = k1_xboole_0 ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_32049,c_88,c_90,c_6261,c_8144]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_55980,plain,
% 11.61/1.98      ( k8_relset_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))),k1_xboole_0)
% 11.61/1.98      | u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.98      | u1_struct_0(sK6) = k1_xboole_0 ),
% 11.61/1.98      inference(light_normalisation,[status(thm)],[c_28254,c_29,c_38544]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_45,plain,
% 11.61/1.98      ( v1_funct_1(sK4(X0,X1)) ),
% 11.61/1.98      inference(cnf_transformation,[],[f162]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_155,plain,
% 11.61/1.98      ( v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_157,plain,
% 11.61/1.98      ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_155]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5,plain,
% 11.61/1.98      ( v1_xboole_0(k1_xboole_0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f119]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_4187,plain,
% 11.61/1.98      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 11.61/1.98      theory(equality) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6287,plain,
% 11.61/1.98      ( v1_funct_1(X0) | ~ v1_funct_1(sK4(X1,X2)) | X0 != sK4(X1,X2) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_4187]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6288,plain,
% 11.61/1.98      ( X0 != sK4(X1,X2)
% 11.61/1.98      | v1_funct_1(X0) = iProver_top
% 11.61/1.98      | v1_funct_1(sK4(X1,X2)) != iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_6287]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_6290,plain,
% 11.61/1.98      ( k1_xboole_0 != sK4(k1_xboole_0,k1_xboole_0)
% 11.61/1.98      | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0)) != iProver_top
% 11.61/1.98      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_6288]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_49,plain,
% 11.61/1.98      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 11.61/1.98      inference(cnf_transformation,[],[f158]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5665,plain,
% 11.61/1.98      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8184,plain,
% 11.61/1.98      ( m1_subset_1(sK4(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_15,c_5665]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9387,plain,
% 11.61/1.98      ( r1_tarski(sK4(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8184,c_5678]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9419,plain,
% 11.61/1.98      ( r1_tarski(sK4(X0,k1_xboole_0),k1_xboole_0) ),
% 11.61/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_9387]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9421,plain,
% 11.61/1.98      ( r1_tarski(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_9419]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_11569,plain,
% 11.61/1.98      ( ~ v1_xboole_0(sK4(X0,X1)) | k1_xboole_0 = sK4(X0,X1) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_6]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_11573,plain,
% 11.61/1.98      ( ~ v1_xboole_0(sK4(k1_xboole_0,k1_xboole_0))
% 11.61/1.98      | k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_11569]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_19,plain,
% 11.61/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.61/1.98      | ~ v1_xboole_0(X1)
% 11.61/1.98      | v1_xboole_0(X0) ),
% 11.61/1.98      inference(cnf_transformation,[],[f133]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_578,plain,
% 11.61/1.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.61/1.98      inference(prop_impl,[status(thm)],[c_20]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_579,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_578]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_704,plain,
% 11.61/1.98      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 11.61/1.98      inference(bin_hyper_res,[status(thm)],[c_19,c_579]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_26537,plain,
% 11.61/1.98      ( ~ r1_tarski(sK4(X0,X1),X2)
% 11.61/1.98      | ~ v1_xboole_0(X2)
% 11.61/1.98      | v1_xboole_0(sK4(X0,X1)) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_704]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_26544,plain,
% 11.61/1.98      ( ~ r1_tarski(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 11.61/1.98      | v1_xboole_0(sK4(k1_xboole_0,k1_xboole_0))
% 11.61/1.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_26537]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_20268,plain,
% 11.61/1.98      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 11.61/1.98      | r1_tarski(k2_relat_1(k1_xboole_0),X0) != iProver_top
% 11.61/1.98      | v1_funct_1(k1_xboole_0) != iProver_top
% 11.61/1.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_29,c_5661]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_20269,plain,
% 11.61/1.98      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 11.61/1.98      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 11.61/1.98      | v1_funct_1(k1_xboole_0) != iProver_top
% 11.61/1.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.61/1.98      inference(light_normalisation,[status(thm)],[c_20268,c_28]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_5676,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.61/1.98      | v1_relat_1(X0) = iProver_top ),
% 11.61/1.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_10230,plain,
% 11.61/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.61/1.98      | v1_relat_1(X0) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_15,c_5676]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_10251,plain,
% 11.61/1.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.61/1.98      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.61/1.98      inference(instantiation,[status(thm)],[c_10230]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_20616,plain,
% 11.61/1.98      ( v1_funct_1(k1_xboole_0) != iProver_top
% 11.61/1.98      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_20269,c_220,c_242,c_10251,c_18870]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_20617,plain,
% 11.61/1.98      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 11.61/1.98      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_20616]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8092,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8037,c_5886]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9190,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 11.61/1.98      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 11.61/1.98      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.98      | v1_funct_1(sK9) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5646,c_5650]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9751,plain,
% 11.61/1.98      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_9190,c_81,c_82,c_83,c_84,c_88,c_89,c_6249,c_6276,
% 11.61/1.98                 c_6641]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9752,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_9751]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9760,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8037,c_9752]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8093,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8037,c_5903]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8096,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0))) = iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8037,c_5739]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_8104,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.61/1.98      inference(demodulation,[status(thm)],[c_8096,c_15]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9759,plain,
% 11.61/1.98      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_5886,c_9752]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9799,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0))) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8037,c_9759]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_9805,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.61/1.98      inference(demodulation,[status(thm)],[c_9799,c_15]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_10789,plain,
% 11.61/1.98      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | u1_struct_0(sK6) = k1_relat_1(sK9) ),
% 11.61/1.98      inference(global_propositional_subsumption,
% 11.61/1.98                [status(thm)],
% 11.61/1.98                [c_9760,c_8093,c_8104,c_9805]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_10790,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.98      inference(renaming,[status(thm)],[c_10789]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_10797,plain,
% 11.61/1.98      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.98      inference(superposition,[status(thm)],[c_8092,c_10790]) ).
% 11.61/1.98  
% 11.61/1.98  cnf(c_28265,plain,
% 11.61/1.98      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.98      | u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.98      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.98      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.98      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8737,c_10797]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_5679,plain,
% 11.61/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.61/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_9460,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_5679,c_8697]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_9828,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_9460,c_5903]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_9878,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8037,c_9828]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_9879,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | r1_tarski(sK9,k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_9878,c_15]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_9386,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | r1_tarski(sK9,k1_xboole_0) = iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8104,c_5678]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_20005,plain,
% 11.61/1.99      ( v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(sK9) ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_9879,c_9386]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_20006,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_20005]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_28247,plain,
% 11.61/1.99      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8737,c_20006]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_28230,plain,
% 11.61/1.99      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8737,c_28060]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_28530,plain,
% 11.61/1.99      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top ),
% 11.61/1.99      inference(forward_subsumption_resolution,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_28230,c_28265]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_29626,plain,
% 11.61/1.99      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | r1_tarski(k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8737,c_29613]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_55942,plain,
% 11.61/1.99      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_28265,c_81,c_82,c_90,c_5730,c_5739,c_6351,c_28247,
% 11.61/1.99                 c_28530,c_29626]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_55946,plain,
% 11.61/1.99      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_xboole_0
% 11.61/1.99      | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.99      inference(light_normalisation,[status(thm)],[c_55942,c_29,c_38544]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_55951,plain,
% 11.61/1.99      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_xboole_0
% 11.61/1.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_20617,c_55946]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_55984,plain,
% 11.61/1.99      ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_xboole_0 ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_55980,c_157,c_5,c_6290,c_9421,c_11573,c_26544,c_55951]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_9384,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))))) = iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8094,c_5678]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_13113,plain,
% 11.61/1.99      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = sK9
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))),sK9) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_9384,c_5687]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_55331,plain,
% 11.61/1.99      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_xboole_0
% 11.61/1.99      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))),k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(light_normalisation,[status(thm)],[c_13113,c_29,c_38544]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_56034,plain,
% 11.61/1.99      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_xboole_0
% 11.61/1.99      | r1_tarski(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0),k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_55984,c_55331]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_56110,plain,
% 11.61/1.99      ( k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_xboole_0
% 11.61/1.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_56034,c_15]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38713,plain,
% 11.61/1.99      ( u1_struct_0(sK7) = k1_xboole_0
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(k1_xboole_0) ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_38544,c_8037]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38762,plain,
% 11.61/1.99      ( u1_struct_0(sK7) = k1_xboole_0 | u1_struct_0(sK6) = k1_xboole_0 ),
% 11.61/1.99      inference(light_normalisation,[status(thm)],[c_38713,c_29]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38720,plain,
% 11.61/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) = iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_38544,c_5646]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_43510,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_38720,c_5649]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_21970,plain,
% 11.61/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.61/1.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_16,c_5674]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_22117,plain,
% 11.61/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_21970,c_6414]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_22118,plain,
% 11.61/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_22117]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_43509,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_38720,c_5650]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6548,plain,
% 11.61/1.99      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),X1)
% 11.61/1.99      | v5_pre_topc(X0,sK6,X1)
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X1))
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X1))))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
% 11.61/1.99      | ~ v2_pre_topc(X1)
% 11.61/1.99      | ~ v2_pre_topc(sK6)
% 11.61/1.99      | ~ l1_pre_topc(X1)
% 11.61/1.99      | ~ l1_pre_topc(sK6)
% 11.61/1.99      | ~ v1_funct_1(X0) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_64]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7276,plain,
% 11.61/1.99      ( ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
% 11.61/1.99      | v5_pre_topc(X0,sK6,sK7)
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 11.61/1.99      | ~ v2_pre_topc(sK7)
% 11.61/1.99      | ~ v2_pre_topc(sK6)
% 11.61/1.99      | ~ l1_pre_topc(sK7)
% 11.61/1.99      | ~ l1_pre_topc(sK6)
% 11.61/1.99      | ~ v1_funct_1(X0) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_6548]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7277,plain,
% 11.61/1.99      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(X0,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_7276]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7279,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_7277]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6558,plain,
% 11.61/1.99      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),X1)
% 11.61/1.99      | ~ v5_pre_topc(X0,sK6,X1)
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X1))
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(X1))))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
% 11.61/1.99      | ~ v2_pre_topc(X1)
% 11.61/1.99      | ~ v2_pre_topc(sK6)
% 11.61/1.99      | ~ l1_pre_topc(X1)
% 11.61/1.99      | ~ l1_pre_topc(sK6)
% 11.61/1.99      | ~ v1_funct_1(X0) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_65]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7316,plain,
% 11.61/1.99      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7)
% 11.61/1.99      | ~ v5_pre_topc(X0,sK6,sK7)
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7))))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 11.61/1.99      | ~ v2_pre_topc(sK7)
% 11.61/1.99      | ~ v2_pre_topc(sK6)
% 11.61/1.99      | ~ l1_pre_topc(sK7)
% 11.61/1.99      | ~ l1_pre_topc(sK6)
% 11.61/1.99      | ~ v1_funct_1(X0) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_6558]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7317,plain,
% 11.61/1.99      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.99      | v5_pre_topc(X0,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_7316]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7319,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_7317]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38595,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_38544,c_27649]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38615,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_38544,c_25627]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38722,plain,
% 11.61/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_38544,c_5739]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38723,plain,
% 11.61/1.99      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_38544,c_5730]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44729,plain,
% 11.61/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_43509,c_81,c_82,c_83,c_84,c_157,c_5,c_6290,c_7279,
% 11.61/1.99                 c_7319,c_9421,c_11573,c_26544,c_38595,c_38615,c_38722,
% 11.61/1.99                 c_38723]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44730,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_44729]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44733,plain,
% 11.61/1.99      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)))) != iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_44730,c_81,c_82,c_83,c_84,c_157,c_5,c_6290,c_7279,
% 11.61/1.99                 c_9421,c_11573,c_26544,c_38615,c_38722,c_38723]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44740,plain,
% 11.61/1.99      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_22118,c_44733]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44760,plain,
% 11.61/1.99      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(sK7)) != iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_43510,c_220,c_242,c_44740]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44765,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_xboole_0
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_38762,c_44760]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_8095,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8037,c_5645]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38708,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_relat_1(k1_xboole_0)
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_38544,c_8095]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38783,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_xboole_0
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.99      inference(light_normalisation,[status(thm)],[c_38708,c_29]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_56044,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_xboole_0
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),k1_xboole_0) = iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_55984,c_38783]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_57478,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_xboole_0 ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_56110,c_44765,c_56044]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_43508,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_38720,c_5651]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_43507,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_38720,c_5652]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6568,plain,
% 11.61/1.99      ( v5_pre_topc(X0,sK6,X1)
% 11.61/1.99      | ~ v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1))
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 11.61/1.99      | ~ v2_pre_topc(X1)
% 11.61/1.99      | ~ v2_pre_topc(sK6)
% 11.61/1.99      | ~ l1_pre_topc(X1)
% 11.61/1.99      | ~ l1_pre_topc(sK6)
% 11.61/1.99      | ~ v1_funct_1(X0) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_66]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7356,plain,
% 11.61/1.99      ( ~ v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 11.61/1.99      | v5_pre_topc(X0,sK6,sK7)
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 11.61/1.99      | ~ v2_pre_topc(sK7)
% 11.61/1.99      | ~ v2_pre_topc(sK6)
% 11.61/1.99      | ~ l1_pre_topc(sK7)
% 11.61/1.99      | ~ l1_pre_topc(sK6)
% 11.61/1.99      | ~ v1_funct_1(X0) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_6568]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7357,plain,
% 11.61/1.99      ( v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(X0,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_7356]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7359,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_7357]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6588,plain,
% 11.61/1.99      ( ~ v5_pre_topc(X0,sK6,X1)
% 11.61/1.99      | v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1))
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 11.61/1.99      | ~ v2_pre_topc(X1)
% 11.61/1.99      | ~ v2_pre_topc(sK6)
% 11.61/1.99      | ~ l1_pre_topc(X1)
% 11.61/1.99      | ~ l1_pre_topc(sK6)
% 11.61/1.99      | ~ v1_funct_1(X0) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_67]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7396,plain,
% 11.61/1.99      ( v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 11.61/1.99      | ~ v5_pre_topc(X0,sK6,sK7)
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 11.61/1.99      | ~ v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 11.61/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
% 11.61/1.99      | ~ v2_pre_topc(sK7)
% 11.61/1.99      | ~ v2_pre_topc(sK6)
% 11.61/1.99      | ~ l1_pre_topc(sK7)
% 11.61/1.99      | ~ l1_pre_topc(sK6)
% 11.61/1.99      | ~ v1_funct_1(X0) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_6588]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7397,plain,
% 11.61/1.99      ( v5_pre_topc(X0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(X0,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_7396]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7399,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_7397]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_10813,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(sK9) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_5646,c_5652]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6245,plain,
% 11.61/1.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 11.61/1.99      | ~ l1_pre_topc(sK7) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_62]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6246,plain,
% 11.61/1.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_6245]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6272,plain,
% 11.61/1.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
% 11.61/1.99      | ~ v2_pre_topc(sK7)
% 11.61/1.99      | ~ l1_pre_topc(sK7) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_63]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6273,plain,
% 11.61/1.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v2_pre_topc(sK7) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK7) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_6272]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6636,plain,
% 11.61/1.99      ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 11.61/1.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_61]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6637,plain,
% 11.61/1.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
% 11.61/1.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_6636]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_11521,plain,
% 11.61/1.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_10813,c_81,c_82,c_83,c_84,c_88,c_89,c_6246,c_6273,
% 11.61/1.99                 c_6637]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_11522,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_11521]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_11532,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8037,c_11522]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_12671,plain,
% 11.61/1.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),k1_xboole_0))) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8036,c_11532]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_12689,plain,
% 11.61/1.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = k1_relat_1(sK9)
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_12671,c_15]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6359,plain,
% 11.61/1.99      ( r1_tarski(k1_relat_1(sK9),u1_struct_0(sK6)) = iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_5739,c_5631]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_11531,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_5886,c_11522]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_23078,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | r1_tarski(k1_relat_1(sK9),u1_struct_0(sK6)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_21966,c_11531]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_27112,plain,
% 11.61/1.99      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | u1_struct_0(sK6) = k1_relat_1(sK9) ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_12689,c_6359,c_8093,c_23078]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_27113,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_27112]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_27120,plain,
% 11.61/1.99      ( u1_struct_0(sK6) = k1_relat_1(sK9)
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_8092,c_27113]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_32153,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_27120,c_6359,c_23078]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38576,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,sK7) = iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_38544,c_32153]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_23061,plain,
% 11.61/1.99      ( r1_tarski(k1_relat_1(sK9),X0) != iProver_top
% 11.61/1.99      | r1_tarski(sK9,k2_zfmisc_1(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) = iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_21966,c_5678]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_9954,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v2_pre_topc(sK6) != iProver_top
% 11.61/1.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | l1_pre_topc(sK6) != iProver_top
% 11.61/1.99      | v1_funct_1(sK9) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_5646,c_5651]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_10329,plain,
% 11.61/1.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_9954,c_81,c_82,c_83,c_84,c_88,c_89,c_6246,c_6273,
% 11.61/1.99                 c_6637]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_10330,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_10329]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_10337,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_5679,c_10330]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_10432,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | r1_tarski(sK9,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_10337,c_5903]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_23667,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | r1_tarski(k1_relat_1(sK9),u1_struct_0(sK6)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_23061,c_10432]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_25998,plain,
% 11.61/1.99      ( v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_23667,c_6359]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_25999,plain,
% 11.61/1.99      ( v5_pre_topc(sK9,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(sK9,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(sK9,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_25998]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38609,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) != iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,sK7) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_38544,c_25999]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44626,plain,
% 11.61/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_43507,c_81,c_82,c_83,c_84,c_157,c_5,c_6290,c_7359,
% 11.61/1.99                 c_7399,c_9421,c_11573,c_26544,c_38576,c_38609,c_38722,
% 11.61/1.99                 c_38723]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44627,plain,
% 11.61/1.99      ( v5_pre_topc(k1_xboole_0,sK6,g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) = iProver_top
% 11.61/1.99      | v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 11.61/1.99      inference(renaming,[status(thm)],[c_44626]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44630,plain,
% 11.61/1.99      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_44627,c_81,c_82,c_83,c_84,c_157,c_5,c_6290,c_7359,
% 11.61/1.99                 c_9421,c_11573,c_26544,c_38609,c_38722,c_38723]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44637,plain,
% 11.61/1.99      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_22118,c_44630]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_44657,plain,
% 11.61/1.99      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK6),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_43508,c_220,c_242,c_44637]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_57518,plain,
% 11.61/1.99      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_57478,c_44657]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_24152,plain,
% 11.61/1.99      ( sK9 = k1_xboole_0
% 11.61/1.99      | v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.99      inference(superposition,[status(thm)],[c_24028,c_5645]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6342,plain,
% 11.61/1.99      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))))
% 11.61/1.99      | r1_tarski(k2_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_953]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6343,plain,
% 11.61/1.99      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))))) != iProver_top
% 11.61/1.99      | r1_tarski(k2_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_6342]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_6396,plain,
% 11.61/1.99      ( v1_funct_2(sK9,k1_relat_1(sK9),X0)
% 11.61/1.99      | ~ r1_tarski(k2_relat_1(sK9),X0)
% 11.61/1.99      | ~ v1_funct_1(sK9)
% 11.61/1.99      | ~ v1_relat_1(sK9) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_54]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7057,plain,
% 11.61/1.99      ( v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 11.61/1.99      | ~ r1_tarski(k2_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))))
% 11.61/1.99      | ~ v1_funct_1(sK9)
% 11.61/1.99      | ~ v1_relat_1(sK9) ),
% 11.61/1.99      inference(instantiation,[status(thm)],[c_6396]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_7058,plain,
% 11.61/1.99      ( v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top
% 11.61/1.99      | r1_tarski(k2_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) != iProver_top
% 11.61/1.99      | v1_funct_1(sK9) != iProver_top
% 11.61/1.99      | v1_relat_1(sK9) != iProver_top ),
% 11.61/1.99      inference(predicate_to_equality,[status(thm)],[c_7057]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_24940,plain,
% 11.61/1.99      ( v1_funct_2(sK9,k1_relat_1(sK9),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.99      inference(global_propositional_subsumption,
% 11.61/1.99                [status(thm)],
% 11.61/1.99                [c_24152,c_88,c_90,c_6261,c_6343,c_7058]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_38623,plain,
% 11.61/1.99      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.99      inference(demodulation,[status(thm)],[c_38544,c_24940]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(c_39206,plain,
% 11.61/1.99      ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))) = iProver_top ),
% 11.61/1.99      inference(light_normalisation,[status(thm)],[c_38623,c_29]) ).
% 11.61/1.99  
% 11.61/1.99  cnf(contradiction,plain,
% 11.61/1.99      ( $false ),
% 11.61/1.99      inference(minisat,[status(thm)],[c_57518,c_39206]) ).
% 11.61/1.99  
% 11.61/1.99  
% 11.61/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.61/1.99  
% 11.61/1.99  ------                               Statistics
% 11.61/1.99  
% 11.61/1.99  ------ General
% 11.61/1.99  
% 11.61/1.99  abstr_ref_over_cycles:                  0
% 11.61/1.99  abstr_ref_under_cycles:                 0
% 11.61/1.99  gc_basic_clause_elim:                   0
% 11.61/1.99  forced_gc_time:                         0
% 11.61/1.99  parsing_time:                           0.014
% 11.61/1.99  unif_index_cands_time:                  0.
% 11.61/1.99  unif_index_add_time:                    0.
% 11.61/1.99  orderings_time:                         0.
% 11.61/1.99  out_proof_time:                         0.044
% 11.61/1.99  total_time:                             1.499
% 11.61/1.99  num_of_symbols:                         68
% 11.61/1.99  num_of_terms:                           34980
% 11.61/1.99  
% 11.61/1.99  ------ Preprocessing
% 11.61/1.99  
% 11.61/1.99  num_of_splits:                          0
% 11.61/1.99  num_of_split_atoms:                     0
% 11.61/1.99  num_of_reused_defs:                     0
% 11.61/1.99  num_eq_ax_congr_red:                    80
% 11.61/1.99  num_of_sem_filtered_clauses:            1
% 11.61/1.99  num_of_subtypes:                        0
% 11.61/1.99  monotx_restored_types:                  0
% 11.61/1.99  sat_num_of_epr_types:                   0
% 11.61/1.99  sat_num_of_non_cyclic_types:            0
% 11.61/1.99  sat_guarded_non_collapsed_types:        0
% 11.61/1.99  num_pure_diseq_elim:                    0
% 11.61/1.99  simp_replaced_by:                       0
% 11.61/1.99  res_preprocessed:                       333
% 11.61/1.99  prep_upred:                             0
% 11.61/1.99  prep_unflattend:                        92
% 11.61/1.99  smt_new_axioms:                         0
% 11.61/1.99  pred_elim_cands:                        11
% 11.61/1.99  pred_elim:                              3
% 11.61/1.99  pred_elim_cl:                           6
% 11.61/1.99  pred_elim_cycles:                       7
% 11.61/1.99  merged_defs:                            24
% 11.61/1.99  merged_defs_ncl:                        0
% 11.61/1.99  bin_hyper_res:                          26
% 11.61/1.99  prep_cycles:                            4
% 11.61/1.99  pred_elim_time:                         0.057
% 11.61/1.99  splitting_time:                         0.
% 11.61/1.99  sem_filter_time:                        0.
% 11.61/1.99  monotx_time:                            0.
% 11.61/1.99  subtype_inf_time:                       0.
% 11.61/1.99  
% 11.61/1.99  ------ Problem properties
% 11.61/1.99  
% 11.61/1.99  clauses:                                71
% 11.61/1.99  conjectures:                            13
% 11.61/1.99  epr:                                    16
% 11.61/1.99  horn:                                   62
% 11.61/1.99  ground:                                 16
% 11.61/1.99  unary:                                  24
% 11.61/1.99  binary:                                 21
% 11.61/1.99  lits:                                   200
% 11.61/1.99  lits_eq:                                21
% 11.61/1.99  fd_pure:                                0
% 11.61/1.99  fd_pseudo:                              0
% 11.61/1.99  fd_cond:                                5
% 11.61/1.99  fd_pseudo_cond:                         4
% 11.61/1.99  ac_symbols:                             0
% 11.61/1.99  
% 11.61/1.99  ------ Propositional Solver
% 11.61/1.99  
% 11.61/1.99  prop_solver_calls:                      29
% 11.61/1.99  prop_fast_solver_calls:                 5496
% 11.61/1.99  smt_solver_calls:                       0
% 11.61/1.99  smt_fast_solver_calls:                  0
% 11.61/1.99  prop_num_of_clauses:                    16193
% 11.61/1.99  prop_preprocess_simplified:             32182
% 11.61/1.99  prop_fo_subsumed:                       436
% 11.61/1.99  prop_solver_time:                       0.
% 11.61/1.99  smt_solver_time:                        0.
% 11.61/1.99  smt_fast_solver_time:                   0.
% 11.61/1.99  prop_fast_solver_time:                  0.
% 11.61/1.99  prop_unsat_core_time:                   0.001
% 11.61/1.99  
% 11.61/1.99  ------ QBF
% 11.61/1.99  
% 11.61/1.99  qbf_q_res:                              0
% 11.61/1.99  qbf_num_tautologies:                    0
% 11.61/1.99  qbf_prep_cycles:                        0
% 11.61/1.99  
% 11.61/1.99  ------ BMC1
% 11.61/1.99  
% 11.61/1.99  bmc1_current_bound:                     -1
% 11.61/1.99  bmc1_last_solved_bound:                 -1
% 11.61/1.99  bmc1_unsat_core_size:                   -1
% 11.61/1.99  bmc1_unsat_core_parents_size:           -1
% 11.61/1.99  bmc1_merge_next_fun:                    0
% 11.61/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.61/1.99  
% 11.61/1.99  ------ Instantiation
% 11.61/1.99  
% 11.61/1.99  inst_num_of_clauses:                    4032
% 11.61/1.99  inst_num_in_passive:                    1729
% 11.61/1.99  inst_num_in_active:                     1436
% 11.61/1.99  inst_num_in_unprocessed:                867
% 11.61/1.99  inst_num_of_loops:                      2070
% 11.61/1.99  inst_num_of_learning_restarts:          0
% 11.61/1.99  inst_num_moves_active_passive:          632
% 11.61/1.99  inst_lit_activity:                      0
% 11.61/1.99  inst_lit_activity_moves:                0
% 11.61/1.99  inst_num_tautologies:                   0
% 11.61/1.99  inst_num_prop_implied:                  0
% 11.61/1.99  inst_num_existing_simplified:           0
% 11.61/1.99  inst_num_eq_res_simplified:             0
% 11.61/1.99  inst_num_child_elim:                    0
% 11.61/1.99  inst_num_of_dismatching_blockings:      3138
% 11.61/1.99  inst_num_of_non_proper_insts:           3698
% 11.61/1.99  inst_num_of_duplicates:                 0
% 11.61/1.99  inst_inst_num_from_inst_to_res:         0
% 11.61/1.99  inst_dismatching_checking_time:         0.
% 11.61/1.99  
% 11.61/1.99  ------ Resolution
% 11.61/1.99  
% 11.61/1.99  res_num_of_clauses:                     0
% 11.61/1.99  res_num_in_passive:                     0
% 11.61/1.99  res_num_in_active:                      0
% 11.61/1.99  res_num_of_loops:                       337
% 11.61/1.99  res_forward_subset_subsumed:            292
% 11.61/1.99  res_backward_subset_subsumed:           26
% 11.61/1.99  res_forward_subsumed:                   0
% 11.61/1.99  res_backward_subsumed:                  0
% 11.61/1.99  res_forward_subsumption_resolution:     0
% 11.61/1.99  res_backward_subsumption_resolution:    0
% 11.61/1.99  res_clause_to_clause_subsumption:       3606
% 11.61/1.99  res_orphan_elimination:                 0
% 11.61/1.99  res_tautology_del:                      244
% 11.61/1.99  res_num_eq_res_simplified:              0
% 11.61/1.99  res_num_sel_changes:                    0
% 11.61/1.99  res_moves_from_active_to_pass:          0
% 11.61/1.99  
% 11.61/1.99  ------ Superposition
% 11.61/1.99  
% 11.61/1.99  sup_time_total:                         0.
% 11.61/1.99  sup_time_generating:                    0.
% 11.61/1.99  sup_time_sim_full:                      0.
% 11.61/1.99  sup_time_sim_immed:                     0.
% 11.61/1.99  
% 11.61/1.99  sup_num_of_clauses:                     858
% 11.61/1.99  sup_num_in_active:                      128
% 11.61/1.99  sup_num_in_passive:                     730
% 11.61/1.99  sup_num_of_loops:                       413
% 11.61/1.99  sup_fw_superposition:                   1048
% 11.61/1.99  sup_bw_superposition:                   815
% 11.61/1.99  sup_immediate_simplified:               593
% 11.61/1.99  sup_given_eliminated:                   0
% 11.61/1.99  comparisons_done:                       0
% 11.61/1.99  comparisons_avoided:                    78
% 11.61/1.99  
% 11.61/1.99  ------ Simplifications
% 11.61/1.99  
% 11.61/1.99  
% 11.61/1.99  sim_fw_subset_subsumed:                 165
% 11.61/1.99  sim_bw_subset_subsumed:                 288
% 11.61/1.99  sim_fw_subsumed:                        115
% 11.61/1.99  sim_bw_subsumed:                        23
% 11.61/1.99  sim_fw_subsumption_res:                 38
% 11.61/1.99  sim_bw_subsumption_res:                 5
% 11.61/1.99  sim_tautology_del:                      37
% 11.61/1.99  sim_eq_tautology_del:                   53
% 11.61/1.99  sim_eq_res_simp:                        0
% 11.61/1.99  sim_fw_demodulated:                     158
% 11.61/1.99  sim_bw_demodulated:                     232
% 11.61/1.99  sim_light_normalised:                   287
% 11.61/1.99  sim_joinable_taut:                      0
% 11.61/1.99  sim_joinable_simp:                      0
% 11.61/1.99  sim_ac_normalised:                      0
% 11.61/1.99  sim_smt_subsumption:                    0
% 11.61/1.99  
%------------------------------------------------------------------------------
