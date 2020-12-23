%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:25 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  194 (7346 expanded)
%              Number of leaves         :   21 (2352 expanded)
%              Depth                    :   56
%              Number of atoms          :  993 (79393 expanded)
%              Number of equality atoms :   25 (5621 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1741,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1739,f68])).

fof(f68,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
      | ~ v5_pre_topc(sK5,sK3,sK4) )
    & ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
      | v5_pre_topc(sK5,sK3,sK4) )
    & sK5 = sK6
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f38,f42,f41,f40,f39])).

fof(f39,plain,
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
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X1)
                    | ~ v5_pre_topc(X2,sK3,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X1)
                    | v5_pre_topc(X2,sK3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X1)
                  | ~ v5_pre_topc(X2,sK3,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X1)
                  | v5_pre_topc(X2,sK3,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
                | ~ v5_pre_topc(X2,sK3,sK4) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
                | v5_pre_topc(X2,sK3,sK4) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
          & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
              | ~ v5_pre_topc(X2,sK3,sK4) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
              | v5_pre_topc(X2,sK3,sK4) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
        & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
            | ~ v5_pre_topc(sK5,sK3,sK4) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
            | v5_pre_topc(sK5,sK3,sK4) )
          & sK5 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
          | ~ v5_pre_topc(sK5,sK3,sK4) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
          | v5_pre_topc(sK5,sK3,sK4) )
        & sK5 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
        | ~ v5_pre_topc(sK5,sK3,sK4) )
      & ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
        | v5_pre_topc(sK5,sK3,sK4) )
      & sK5 = sK6
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
      & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f1739,plain,(
    ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f1732,f134])).

fof(f134,plain,(
    ! [X2] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f111,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f1732,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f1731,f70])).

fof(f70,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f1731,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f1730,f737])).

fof(f737,plain,(
    ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) ),
    inference(subsumption_resolution,[],[f121,f736])).

fof(f736,plain,(
    v5_pre_topc(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f735,f68])).

fof(f735,plain,
    ( v5_pre_topc(sK5,sK3,sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f734,f70])).

fof(f734,plain,
    ( v5_pre_topc(sK5,sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f733,f72])).

fof(f72,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f733,plain,
    ( v5_pre_topc(sK5,sK3,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f732,f73])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f732,plain,
    ( v5_pre_topc(sK5,sK3,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(duplicate_literal_removal,[],[f729])).

fof(f729,plain,
    ( v5_pre_topc(sK5,sK3,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f728,f480])).

fof(f480,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,sK10(X0,X1,sK5)),X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK5,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f99,f124])).

fof(f124,plain,(
    v1_funct_1(sK5) ),
    inference(forward_demodulation,[],[f74,f77])).

fof(f77,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK10(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK10(X0,X1,X2)),X0)
                    & v4_pre_topc(sK10(X0,X1,X2),X1)
                    & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK10(X0,X1,X2)),X0)
        & v4_pre_topc(sK10(X0,X1,X2),X1)
        & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f728,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3)
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f726,f73])).

fof(f726,plain,
    ( v5_pre_topc(sK5,sK3,sK4)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(resolution,[],[f721,f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f721,plain,
    ( ~ m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | v5_pre_topc(sK5,sK3,sK4)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3) ),
    inference(forward_demodulation,[],[f720,f536])).

fof(f536,plain,(
    u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f230,f535])).

fof(f535,plain,(
    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK3)) ),
    inference(resolution,[],[f530,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f530,plain,(
    m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f528,f68])).

fof(f528,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f527,f134])).

fof(f527,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f526,f118])).

fof(f118,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f526,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(resolution,[],[f525,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f525,plain,
    ( ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f524,f67])).

fof(f67,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f524,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f523,f68])).

fof(f523,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f378,f102])).

fof(f102,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f378,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) ),
    inference(resolution,[],[f344,f158])).

fof(f158,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f156,f125])).

fof(f125,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f81,f95])).

fof(f95,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f35,f34,f33])).

fof(f33,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ( sP0(X0)
        & ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP1(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f81,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ v2_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP1(X0) )
        & ( sP1(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f156,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X0),X0) ) ),
    inference(subsumption_resolution,[],[f155,f118])).

fof(f155,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ sP1(X0)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f143,f116])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ sP1(X0) ) ),
    inference(resolution,[],[f101,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
          & r1_tarski(sK7(X0),u1_pre_topc(X0))
          & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X2] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r1_tarski(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
        & r1_tarski(sK7(X0),u1_pre_topc(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X1] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            & r1_tarski(X1,u1_pre_topc(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X2] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r1_tarski(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

% (4417)Refutation not found, incomplete strategy% (4417)------------------------------
% (4417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4417)Termination reason: Refutation not found, incomplete strategy

% (4417)Memory used [KB]: 6140
% (4417)Time elapsed: 0.249 s
% (4417)------------------------------
% (4417)------------------------------
fof(f344,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f341,f68])).

fof(f341,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ l1_pre_topc(sK3)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f106,f67])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f230,plain,
    ( ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK3))
    | u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(resolution,[],[f229,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f229,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(subsumption_resolution,[],[f228,f118])).

fof(f228,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(resolution,[],[f227,f116])).

fof(f227,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(resolution,[],[f217,f115])).

fof(f217,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f216,f67])).

fof(f216,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f209,f68])).

fof(f209,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f191,f158])).

fof(f191,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) ) ),
    inference(subsumption_resolution,[],[f188,f68])).

fof(f188,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v3_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK3)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) ) ),
    inference(resolution,[],[f104,f67])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f720,plain,
    ( v5_pre_topc(sK5,sK3,sK4)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3) ),
    inference(subsumption_resolution,[],[f719,f67])).

fof(f719,plain,
    ( v5_pre_topc(sK5,sK3,sK4)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f713,f68])).

fof(f713,plain,
    ( v5_pre_topc(sK5,sK3,sK4)
    | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f711,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

fof(f711,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f710,f453])).

fof(f453,plain,
    ( m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f452,f68])).

fof(f452,plain,
    ( m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f451,f70])).

fof(f451,plain,
    ( m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f449,f73])).

fof(f449,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f448,f72])).

fof(f448,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(sK10(X0,X1,sK5),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(sK5,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f97,f124])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f710,plain,
    ( ~ m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(duplicate_literal_removal,[],[f708])).

fof(f708,plain,
    ( ~ m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK3,sK4)
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(resolution,[],[f707,f431])).

fof(f431,plain,
    ( v4_pre_topc(sK10(sK3,sK4,sK5),sK4)
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(subsumption_resolution,[],[f430,f68])).

fof(f430,plain,
    ( v4_pre_topc(sK10(sK3,sK4,sK5),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f429,f70])).

fof(f429,plain,
    ( v4_pre_topc(sK10(sK3,sK4,sK5),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f427,f73])).

fof(f427,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | v4_pre_topc(sK10(sK3,sK4,sK5),sK4)
    | v5_pre_topc(sK5,sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f426,f72])).

fof(f426,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v4_pre_topc(sK10(X0,X1,sK5),X1)
      | v5_pre_topc(sK5,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f98,f124])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | v4_pre_topc(sK10(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f707,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK5,sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f705,f68])).

fof(f705,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK5,sK3,sK4)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f704,f134])).

fof(f704,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK5,sK3,sK4) ) ),
    inference(forward_demodulation,[],[f703,f536])).

fof(f703,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK5,sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f702,f72])).

fof(f702,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK5,sK3,sK4) ) ),
    inference(forward_demodulation,[],[f701,f536])).

fof(f701,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK5,sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f700,f73])).

fof(f700,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK5,sK3,sK4) ) ),
    inference(forward_demodulation,[],[f699,f536])).

fof(f699,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK5,sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f698,f70])).

fof(f698,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ l1_pre_topc(sK4)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK5,sK3,sK4) ) ),
    inference(resolution,[],[f514,f120])).

fof(f120,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(backward_demodulation,[],[f78,f77])).

fof(f78,plain,
    ( v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f514,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(sK5,X2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK5,X0),X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f96,f124])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f121,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK4)
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) ),
    inference(backward_demodulation,[],[f79,f77])).

fof(f79,plain,
    ( ~ v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f1730,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f1729,f72])).

fof(f1729,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f1724,f73])).

fof(f1724,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(resolution,[],[f1340,f755])).

fof(f755,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5)),sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f754,f739])).

fof(f739,plain,
    ( m1_subset_1(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f458,f737])).

fof(f458,plain,
    ( m1_subset_1(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f457,f70])).

fof(f457,plain,
    ( m1_subset_1(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f450,f122])).

fof(f122,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
    inference(forward_demodulation,[],[f76,f77])).

fof(f76,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f450,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | m1_subset_1(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(resolution,[],[f448,f123])).

fof(f123,plain,(
    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f75,f77])).

fof(f75,plain,(
    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f754,plain,
    ( ~ m1_subset_1(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5)),sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(resolution,[],[f750,f738])).

fof(f738,plain,
    ( v4_pre_topc(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f433,f737])).

fof(f433,plain,
    ( v4_pre_topc(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f432,f70])).

fof(f432,plain,
    ( v4_pre_topc(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f428,f122])).

fof(f428,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))
    | v4_pre_topc(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),sK4)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(resolution,[],[f426,f123])).

fof(f750,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f749,f68])).

fof(f749,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(subsumption_resolution,[],[f748,f70])).

fof(f748,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
      | ~ l1_pre_topc(sK4)
      | ~ l1_pre_topc(sK3) ) ),
    inference(subsumption_resolution,[],[f747,f72])).

fof(f747,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
      | ~ l1_pre_topc(sK4)
      | ~ l1_pre_topc(sK3) ) ),
    inference(subsumption_resolution,[],[f746,f73])).

fof(f746,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v4_pre_topc(X0,sK4)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)
      | ~ l1_pre_topc(sK4)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f736,f514])).

fof(f1340,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(X0))
      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f1339,f117])).

fof(f1339,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3)
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(X0))
      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f1338,f536])).

fof(f1338,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3)
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(X0))
      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)))) ) ),
    inference(forward_demodulation,[],[f1337,f536])).

fof(f1337,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(X0))
      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)))) ) ),
    inference(forward_demodulation,[],[f1336,f536])).

fof(f1336,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(X0))
      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)))) ) ),
    inference(forward_demodulation,[],[f1335,f536])).

fof(f1335,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))
      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f1329,f68])).

fof(f1329,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))
      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3)
      | ~ l1_pre_topc(sK3)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)))) ) ),
    inference(resolution,[],[f492,f67])).

fof(f492,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),sK5,sK10(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1,sK5)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),sK5,sK10(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1,sK5)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) ) ),
    inference(subsumption_resolution,[],[f491,f134])).

fof(f491,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),sK5,sK10(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1,sK5)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),sK5,sK10(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1,sK5)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f480,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:40:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (4420)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (4411)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (4429)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (4412)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (4413)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (4413)Refutation not found, incomplete strategy% (4413)------------------------------
% 0.20/0.51  % (4413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4428)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (4430)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (4410)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (4408)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (4432)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (4421)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (4413)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4413)Memory used [KB]: 6140
% 0.20/0.51  % (4413)Time elapsed: 0.083 s
% 0.20/0.51  % (4413)------------------------------
% 0.20/0.51  % (4413)------------------------------
% 0.20/0.51  % (4415)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (4431)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (4425)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (4419)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (4422)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (4427)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (4409)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (4418)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (4416)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (4409)Refutation not found, incomplete strategy% (4409)------------------------------
% 0.20/0.53  % (4409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4409)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4409)Memory used [KB]: 10746
% 0.20/0.53  % (4409)Time elapsed: 0.116 s
% 0.20/0.53  % (4409)------------------------------
% 0.20/0.53  % (4409)------------------------------
% 0.20/0.53  % (4434)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (4426)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (4423)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (4414)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.55  % (4414)Refutation not found, incomplete strategy% (4414)------------------------------
% 0.20/0.55  % (4414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (4414)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (4414)Memory used [KB]: 10618
% 0.20/0.55  % (4414)Time elapsed: 0.126 s
% 0.20/0.55  % (4414)------------------------------
% 0.20/0.55  % (4414)------------------------------
% 0.20/0.55  % (4433)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % (4419)Refutation not found, incomplete strategy% (4419)------------------------------
% 0.20/0.55  % (4419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (4417)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.52/0.57  % (4419)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (4419)Memory used [KB]: 11129
% 1.52/0.57  % (4419)Time elapsed: 0.145 s
% 1.52/0.57  % (4419)------------------------------
% 1.52/0.57  % (4419)------------------------------
% 2.25/0.65  % (4411)Refutation found. Thanks to Tanya!
% 2.25/0.65  % SZS status Theorem for theBenchmark
% 2.25/0.65  % SZS output start Proof for theBenchmark
% 2.25/0.65  fof(f1741,plain,(
% 2.25/0.65    $false),
% 2.25/0.65    inference(subsumption_resolution,[],[f1739,f68])).
% 2.25/0.65  fof(f68,plain,(
% 2.25/0.65    l1_pre_topc(sK3)),
% 2.25/0.65    inference(cnf_transformation,[],[f43])).
% 2.25/0.65  fof(f43,plain,(
% 2.25/0.65    ((((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = sK6 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 2.25/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f38,f42,f41,f40,f39])).
% 2.25/0.65  fof(f39,plain,(
% 2.25/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X1) | ~v5_pre_topc(X2,sK3,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X1) | v5_pre_topc(X2,sK3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 2.25/0.65    introduced(choice_axiom,[])).
% 2.25/0.65  fof(f40,plain,(
% 2.25/0.65    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X1) | ~v5_pre_topc(X2,sK3,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X1) | v5_pre_topc(X2,sK3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v5_pre_topc(X2,sK3,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(X2,sK3,sK4)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 2.25/0.65    introduced(choice_axiom,[])).
% 2.25/0.65  fof(f41,plain,(
% 2.25/0.65    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v5_pre_topc(X2,sK3,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(X2,sK3,sK4)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5))),
% 2.25/0.65    introduced(choice_axiom,[])).
% 2.25/0.65  fof(f42,plain,(
% 2.25/0.65    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) & v1_funct_1(X3)) => ((~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v5_pre_topc(sK5,sK3,sK4)) & (v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4)) & sK5 = sK6 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) & v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) & v1_funct_1(sK6))),
% 2.25/0.65    introduced(choice_axiom,[])).
% 2.25/0.65  fof(f38,plain,(
% 2.25/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.25/0.65    inference(flattening,[],[f37])).
% 2.25/0.65  fof(f37,plain,(
% 2.25/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.25/0.65    inference(nnf_transformation,[],[f18])).
% 2.25/0.65  fof(f18,plain,(
% 2.25/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.25/0.65    inference(flattening,[],[f17])).
% 2.25/0.65  fof(f17,plain,(
% 2.25/0.65    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.25/0.65    inference(ennf_transformation,[],[f13])).
% 2.25/0.65  fof(f13,negated_conjecture,(
% 2.25/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.25/0.65    inference(negated_conjecture,[],[f12])).
% 2.25/0.65  fof(f12,conjecture,(
% 2.25/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 2.25/0.65  fof(f1739,plain,(
% 2.25/0.65    ~l1_pre_topc(sK3)),
% 2.25/0.65    inference(resolution,[],[f1732,f134])).
% 2.25/0.65  fof(f134,plain,(
% 2.25/0.65    ( ! [X2] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X2)) )),
% 2.25/0.65    inference(resolution,[],[f111,f80])).
% 2.25/0.65  fof(f80,plain,(
% 2.25/0.65    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f19])).
% 2.25/0.65  fof(f19,plain,(
% 2.25/0.65    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.25/0.65    inference(ennf_transformation,[],[f8])).
% 2.25/0.65  fof(f8,axiom,(
% 2.25/0.65    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 2.25/0.65  fof(f111,plain,(
% 2.25/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 2.25/0.65    inference(cnf_transformation,[],[f31])).
% 2.25/0.65  fof(f31,plain,(
% 2.25/0.65    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.25/0.65    inference(ennf_transformation,[],[f15])).
% 2.25/0.65  fof(f15,plain,(
% 2.25/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 2.25/0.65    inference(pure_predicate_removal,[],[f7])).
% 2.25/0.65  fof(f7,axiom,(
% 2.25/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 2.25/0.65  fof(f1732,plain,(
% 2.25/0.65    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.65    inference(subsumption_resolution,[],[f1731,f70])).
% 2.25/0.65  fof(f70,plain,(
% 2.25/0.65    l1_pre_topc(sK4)),
% 2.25/0.65    inference(cnf_transformation,[],[f43])).
% 2.25/0.65  fof(f1731,plain,(
% 2.25/0.65    ~l1_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.65    inference(subsumption_resolution,[],[f1730,f737])).
% 2.25/0.65  fof(f737,plain,(
% 2.25/0.65    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)),
% 2.25/0.65    inference(subsumption_resolution,[],[f121,f736])).
% 2.25/0.65  fof(f736,plain,(
% 2.25/0.65    v5_pre_topc(sK5,sK3,sK4)),
% 2.25/0.65    inference(subsumption_resolution,[],[f735,f68])).
% 2.25/0.65  fof(f735,plain,(
% 2.25/0.65    v5_pre_topc(sK5,sK3,sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.65    inference(subsumption_resolution,[],[f734,f70])).
% 2.25/0.65  fof(f734,plain,(
% 2.25/0.65    v5_pre_topc(sK5,sK3,sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.65    inference(subsumption_resolution,[],[f733,f72])).
% 2.25/0.65  fof(f72,plain,(
% 2.25/0.65    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 2.25/0.65    inference(cnf_transformation,[],[f43])).
% 2.25/0.65  fof(f733,plain,(
% 2.25/0.65    v5_pre_topc(sK5,sK3,sK4) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.65    inference(subsumption_resolution,[],[f732,f73])).
% 2.25/0.65  fof(f73,plain,(
% 2.25/0.65    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 2.25/0.65    inference(cnf_transformation,[],[f43])).
% 2.25/0.65  fof(f732,plain,(
% 2.25/0.65    v5_pre_topc(sK5,sK3,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.65    inference(duplicate_literal_removal,[],[f729])).
% 2.25/0.65  fof(f729,plain,(
% 2.25/0.65    v5_pre_topc(sK5,sK3,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | v5_pre_topc(sK5,sK3,sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.65    inference(resolution,[],[f728,f480])).
% 2.25/0.65  fof(f480,plain,(
% 2.25/0.65    ( ! [X0,X1] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,sK10(X0,X1,sK5)),X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK5,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.25/0.65    inference(resolution,[],[f99,f124])).
% 2.25/0.65  fof(f124,plain,(
% 2.25/0.65    v1_funct_1(sK5)),
% 2.25/0.65    inference(forward_demodulation,[],[f74,f77])).
% 2.25/0.65  fof(f77,plain,(
% 2.25/0.65    sK5 = sK6),
% 2.25/0.65    inference(cnf_transformation,[],[f43])).
% 2.25/0.65  fof(f74,plain,(
% 2.25/0.65    v1_funct_1(sK6)),
% 2.25/0.65    inference(cnf_transformation,[],[f43])).
% 2.25/0.65  fof(f99,plain,(
% 2.25/0.65    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK10(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.25/0.65    inference(cnf_transformation,[],[f58])).
% 2.25/0.65  fof(f58,plain,(
% 2.25/0.65    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK10(X0,X1,X2)),X0) & v4_pre_topc(sK10(X0,X1,X2),X1) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f56,f57])).
% 2.25/0.65  fof(f57,plain,(
% 2.25/0.65    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK10(X0,X1,X2)),X0) & v4_pre_topc(sK10(X0,X1,X2),X1) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.25/0.65    introduced(choice_axiom,[])).
% 2.25/0.65  fof(f56,plain,(
% 2.25/0.65    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.65    inference(rectify,[],[f55])).
% 2.25/0.65  fof(f55,plain,(
% 2.25/0.65    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.65    inference(nnf_transformation,[],[f23])).
% 2.25/0.65  fof(f23,plain,(
% 2.25/0.65    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.65    inference(flattening,[],[f22])).
% 2.25/0.65  fof(f22,plain,(
% 2.25/0.65    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.25/0.65    inference(ennf_transformation,[],[f4])).
% 2.25/0.65  fof(f4,axiom,(
% 2.25/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 2.25/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).
% 2.25/0.65  fof(f728,plain,(
% 2.25/0.65    v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3) | v5_pre_topc(sK5,sK3,sK4)),
% 2.25/0.65    inference(subsumption_resolution,[],[f726,f73])).
% 2.25/0.65  fof(f726,plain,(
% 2.25/0.65    v5_pre_topc(sK5,sK3,sK4) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 2.25/0.65    inference(resolution,[],[f721,f117])).
% 2.25/0.66  fof(f117,plain,(
% 2.25/0.66    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.25/0.66    inference(cnf_transformation,[],[f32])).
% 2.25/0.66  fof(f32,plain,(
% 2.25/0.66    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.66    inference(ennf_transformation,[],[f3])).
% 2.25/0.66  fof(f3,axiom,(
% 2.25/0.66    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 2.25/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 2.25/0.66  fof(f721,plain,(
% 2.25/0.66    ~m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | v5_pre_topc(sK5,sK3,sK4) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3)),
% 2.25/0.66    inference(forward_demodulation,[],[f720,f536])).
% 2.25/0.66  fof(f536,plain,(
% 2.25/0.66    u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.66    inference(subsumption_resolution,[],[f230,f535])).
% 2.25/0.66  fof(f535,plain,(
% 2.25/0.66    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK3))),
% 2.25/0.66    inference(resolution,[],[f530,f115])).
% 2.25/0.66  fof(f115,plain,(
% 2.25/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.25/0.66    inference(cnf_transformation,[],[f66])).
% 2.25/0.66  fof(f66,plain,(
% 2.25/0.66    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.25/0.66    inference(nnf_transformation,[],[f2])).
% 2.25/0.66  fof(f2,axiom,(
% 2.25/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.25/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.25/0.66  fof(f530,plain,(
% 2.25/0.66    m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.25/0.66    inference(subsumption_resolution,[],[f528,f68])).
% 2.25/0.66  fof(f528,plain,(
% 2.25/0.66    m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3)),
% 2.25/0.66    inference(resolution,[],[f527,f134])).
% 2.25/0.66  fof(f527,plain,(
% 2.25/0.66    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.25/0.66    inference(subsumption_resolution,[],[f526,f118])).
% 2.25/0.66  fof(f118,plain,(
% 2.25/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.25/0.66    inference(equality_resolution,[],[f113])).
% 2.25/0.66  fof(f113,plain,(
% 2.25/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.25/0.66    inference(cnf_transformation,[],[f65])).
% 2.25/0.66  fof(f65,plain,(
% 2.25/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.25/0.66    inference(flattening,[],[f64])).
% 2.25/0.66  fof(f64,plain,(
% 2.25/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.25/0.66    inference(nnf_transformation,[],[f1])).
% 2.25/0.66  fof(f1,axiom,(
% 2.25/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.25/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.25/0.66  fof(f526,plain,(
% 2.25/0.66    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 2.25/0.66    inference(resolution,[],[f525,f116])).
% 2.25/0.66  fof(f116,plain,(
% 2.25/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.25/0.66    inference(cnf_transformation,[],[f66])).
% 2.25/0.66  fof(f525,plain,(
% 2.25/0.66    ~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.25/0.66    inference(subsumption_resolution,[],[f524,f67])).
% 2.25/0.66  fof(f67,plain,(
% 2.25/0.66    v2_pre_topc(sK3)),
% 2.25/0.66    inference(cnf_transformation,[],[f43])).
% 2.25/0.67  fof(f524,plain,(
% 2.25/0.67    m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | ~v2_pre_topc(sK3)),
% 2.25/0.67    inference(subsumption_resolution,[],[f523,f68])).
% 2.25/0.67  fof(f523,plain,(
% 2.25/0.67    m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 2.25/0.67    inference(resolution,[],[f378,f102])).
% 2.25/0.67  fof(f102,plain,(
% 2.25/0.67    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f26])).
% 2.25/0.67  fof(f26,plain,(
% 2.25/0.67    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.25/0.67    inference(flattening,[],[f25])).
% 2.25/0.67  fof(f25,plain,(
% 2.25/0.67    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.25/0.67    inference(ennf_transformation,[],[f16])).
% 2.25/0.67  fof(f16,plain,(
% 2.25/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 2.25/0.67    inference(pure_predicate_removal,[],[f9])).
% 2.25/0.67  fof(f9,axiom,(
% 2.25/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 2.25/0.67  fof(f378,plain,(
% 2.25/0.67    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))),
% 2.25/0.67    inference(resolution,[],[f344,f158])).
% 2.25/0.67  fof(f158,plain,(
% 2.25/0.67    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.25/0.67    inference(duplicate_literal_removal,[],[f157])).
% 2.25/0.67  fof(f157,plain,(
% 2.25/0.67    ( ! [X0] : (~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X0),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(resolution,[],[f156,f125])).
% 2.25/0.67  fof(f125,plain,(
% 2.25/0.67    ( ! [X0] : (sP1(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(resolution,[],[f81,f95])).
% 2.25/0.67  fof(f95,plain,(
% 2.25/0.67    ( ! [X0] : (sP2(X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f36])).
% 2.25/0.67  fof(f36,plain,(
% 2.25/0.67    ! [X0] : (sP2(X0) | ~l1_pre_topc(X0))),
% 2.25/0.67    inference(definition_folding,[],[f21,f35,f34,f33])).
% 2.25/0.67  fof(f33,plain,(
% 2.25/0.67    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.25/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.25/0.67  fof(f34,plain,(
% 2.25/0.67    ! [X0] : (sP1(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 2.25/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.25/0.67  fof(f35,plain,(
% 2.25/0.67    ! [X0] : ((v2_pre_topc(X0) <=> sP1(X0)) | ~sP2(X0))),
% 2.25/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.25/0.67  fof(f21,plain,(
% 2.25/0.67    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.25/0.67    inference(flattening,[],[f20])).
% 2.25/0.67  fof(f20,plain,(
% 2.25/0.67    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.25/0.67    inference(ennf_transformation,[],[f14])).
% 2.25/0.67  fof(f14,plain,(
% 2.25/0.67    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.25/0.67    inference(rectify,[],[f5])).
% 2.25/0.67  fof(f5,axiom,(
% 2.25/0.67    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 2.25/0.67  fof(f81,plain,(
% 2.25/0.67    ( ! [X0] : (~sP2(X0) | ~v2_pre_topc(X0) | sP1(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f44])).
% 2.25/0.67  fof(f44,plain,(
% 2.25/0.67    ! [X0] : (((v2_pre_topc(X0) | ~sP1(X0)) & (sP1(X0) | ~v2_pre_topc(X0))) | ~sP2(X0))),
% 2.25/0.67    inference(nnf_transformation,[],[f35])).
% 2.25/0.67  fof(f156,plain,(
% 2.25/0.67    ( ! [X0] : (~sP1(X0) | ~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X0),X0)) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f155,f118])).
% 2.25/0.67  fof(f155,plain,(
% 2.25/0.67    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~sP1(X0) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(X0))) )),
% 2.25/0.67    inference(resolution,[],[f143,f116])).
% 2.25/0.67  fof(f143,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~sP1(X0)) )),
% 2.25/0.67    inference(resolution,[],[f101,f83])).
% 2.25/0.67  fof(f83,plain,(
% 2.25/0.67    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP1(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f49])).
% 2.25/0.67  fof(f49,plain,(
% 2.25/0.67    ! [X0] : ((sP1(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 2.25/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).
% 2.25/0.67  fof(f48,plain,(
% 2.25/0.67    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.25/0.67    introduced(choice_axiom,[])).
% 2.25/0.67  fof(f47,plain,(
% 2.25/0.67    ! [X0] : ((sP1(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 2.25/0.67    inference(rectify,[],[f46])).
% 2.25/0.67  fof(f46,plain,(
% 2.25/0.67    ! [X0] : ((sP1(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 2.25/0.67    inference(flattening,[],[f45])).
% 2.25/0.67  fof(f45,plain,(
% 2.25/0.67    ! [X0] : ((sP1(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 2.25/0.67    inference(nnf_transformation,[],[f34])).
% 2.25/0.67  fof(f101,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f59])).
% 2.25/0.67  fof(f59,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.25/0.67    inference(nnf_transformation,[],[f24])).
% 2.25/0.67  fof(f24,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.25/0.67    inference(ennf_transformation,[],[f6])).
% 2.25/0.67  fof(f6,axiom,(
% 2.25/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 2.25/0.67  % (4417)Refutation not found, incomplete strategy% (4417)------------------------------
% 2.25/0.67  % (4417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.67  % (4417)Termination reason: Refutation not found, incomplete strategy
% 2.25/0.67  
% 2.25/0.67  % (4417)Memory used [KB]: 6140
% 2.25/0.67  % (4417)Time elapsed: 0.249 s
% 2.25/0.67  % (4417)------------------------------
% 2.25/0.67  % (4417)------------------------------
% 2.25/0.67  fof(f344,plain,(
% 2.25/0.67    ( ! [X0] : (~v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f341,f68])).
% 2.25/0.67  fof(f341,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | ~v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(sK3) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 2.25/0.67    inference(resolution,[],[f106,f67])).
% 2.25/0.67  fof(f106,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.25/0.67    inference(cnf_transformation,[],[f61])).
% 2.25/0.67  fof(f61,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.25/0.67    inference(flattening,[],[f60])).
% 2.25/0.67  fof(f60,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.25/0.67    inference(nnf_transformation,[],[f28])).
% 2.25/0.67  fof(f28,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.25/0.67    inference(flattening,[],[f27])).
% 2.25/0.67  fof(f27,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.25/0.67    inference(ennf_transformation,[],[f10])).
% 2.25/0.67  fof(f10,axiom,(
% 2.25/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).
% 2.25/0.67  fof(f230,plain,(
% 2.25/0.67    ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK3)) | u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(resolution,[],[f229,f114])).
% 2.25/0.67  fof(f114,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.25/0.67    inference(cnf_transformation,[],[f65])).
% 2.25/0.67  fof(f229,plain,(
% 2.25/0.67    r1_tarski(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 2.25/0.67    inference(subsumption_resolution,[],[f228,f118])).
% 2.25/0.67  fof(f228,plain,(
% 2.25/0.67    r1_tarski(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))),
% 2.25/0.67    inference(resolution,[],[f227,f116])).
% 2.25/0.67  fof(f227,plain,(
% 2.25/0.67    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | r1_tarski(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 2.25/0.67    inference(resolution,[],[f217,f115])).
% 2.25/0.67  fof(f217,plain,(
% 2.25/0.67    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.25/0.67    inference(subsumption_resolution,[],[f216,f67])).
% 2.25/0.67  fof(f216,plain,(
% 2.25/0.67    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | ~v2_pre_topc(sK3)),
% 2.25/0.67    inference(subsumption_resolution,[],[f209,f68])).
% 2.25/0.67  fof(f209,plain,(
% 2.25/0.67    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 2.25/0.67    inference(resolution,[],[f191,f158])).
% 2.25/0.67  fof(f191,plain,(
% 2.25/0.67    ( ! [X0] : (~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f188,f68])).
% 2.25/0.67  fof(f188,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(X0,sK3) | ~l1_pre_topc(sK3) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) )),
% 2.25/0.67    inference(resolution,[],[f104,f67])).
% 2.25/0.67  fof(f104,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) )),
% 2.25/0.67    inference(cnf_transformation,[],[f61])).
% 2.25/0.67  fof(f720,plain,(
% 2.25/0.67    v5_pre_topc(sK5,sK3,sK4) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3)),
% 2.25/0.67    inference(subsumption_resolution,[],[f719,f67])).
% 2.25/0.67  fof(f719,plain,(
% 2.25/0.67    v5_pre_topc(sK5,sK3,sK4) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3) | ~v2_pre_topc(sK3)),
% 2.25/0.67    inference(subsumption_resolution,[],[f713,f68])).
% 2.25/0.67  fof(f713,plain,(
% 2.25/0.67    v5_pre_topc(sK5,sK3,sK4) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 2.25/0.67    inference(resolution,[],[f711,f109])).
% 2.25/0.67  fof(f109,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f63])).
% 2.25/0.67  fof(f63,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.25/0.67    inference(flattening,[],[f62])).
% 2.25/0.67  fof(f62,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.25/0.67    inference(nnf_transformation,[],[f30])).
% 2.25/0.67  fof(f30,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.25/0.67    inference(flattening,[],[f29])).
% 2.25/0.67  fof(f29,plain,(
% 2.25/0.67    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.25/0.67    inference(ennf_transformation,[],[f11])).
% 2.25/0.67  fof(f11,axiom,(
% 2.25/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).
% 2.25/0.67  fof(f711,plain,(
% 2.25/0.67    v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4)),
% 2.25/0.67    inference(subsumption_resolution,[],[f710,f453])).
% 2.25/0.67  fof(f453,plain,(
% 2.25/0.67    m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v5_pre_topc(sK5,sK3,sK4)),
% 2.25/0.67    inference(subsumption_resolution,[],[f452,f68])).
% 2.25/0.67  fof(f452,plain,(
% 2.25/0.67    m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v5_pre_topc(sK5,sK3,sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.67    inference(subsumption_resolution,[],[f451,f70])).
% 2.25/0.67  fof(f451,plain,(
% 2.25/0.67    m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v5_pre_topc(sK5,sK3,sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.67    inference(subsumption_resolution,[],[f449,f73])).
% 2.25/0.67  fof(f449,plain,(
% 2.25/0.67    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v5_pre_topc(sK5,sK3,sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.67    inference(resolution,[],[f448,f72])).
% 2.25/0.67  fof(f448,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | m1_subset_1(sK10(X0,X1,sK5),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(sK5,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(resolution,[],[f97,f124])).
% 2.25/0.67  fof(f97,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f58])).
% 2.25/0.67  fof(f710,plain,(
% 2.25/0.67    ~m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4)),
% 2.25/0.67    inference(duplicate_literal_removal,[],[f708])).
% 2.25/0.67  fof(f708,plain,(
% 2.25/0.67    ~m1_subset_1(sK10(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(sK3,sK4,sK5)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4) | v5_pre_topc(sK5,sK3,sK4)),
% 2.25/0.67    inference(resolution,[],[f707,f431])).
% 2.25/0.67  fof(f431,plain,(
% 2.25/0.67    v4_pre_topc(sK10(sK3,sK4,sK5),sK4) | v5_pre_topc(sK5,sK3,sK4)),
% 2.25/0.67    inference(subsumption_resolution,[],[f430,f68])).
% 2.25/0.67  fof(f430,plain,(
% 2.25/0.67    v4_pre_topc(sK10(sK3,sK4,sK5),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.67    inference(subsumption_resolution,[],[f429,f70])).
% 2.25/0.67  fof(f429,plain,(
% 2.25/0.67    v4_pre_topc(sK10(sK3,sK4,sK5),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.67    inference(subsumption_resolution,[],[f427,f73])).
% 2.25/0.67  fof(f427,plain,(
% 2.25/0.67    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | v4_pre_topc(sK10(sK3,sK4,sK5),sK4) | v5_pre_topc(sK5,sK3,sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 2.25/0.67    inference(resolution,[],[f426,f72])).
% 2.25/0.67  fof(f426,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v4_pre_topc(sK10(X0,X1,sK5),X1) | v5_pre_topc(sK5,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(resolution,[],[f98,f124])).
% 2.25/0.67  fof(f98,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | v4_pre_topc(sK10(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f58])).
% 2.25/0.67  fof(f707,plain,(
% 2.25/0.67    ( ! [X0] : (~v4_pre_topc(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4)) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f705,f68])).
% 2.25/0.67  fof(f705,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4) | ~l1_pre_topc(sK3)) )),
% 2.25/0.67    inference(resolution,[],[f704,f134])).
% 2.25/0.67  fof(f704,plain,(
% 2.25/0.67    ( ! [X0] : (~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4)) )),
% 2.25/0.67    inference(forward_demodulation,[],[f703,f536])).
% 2.25/0.67  fof(f703,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4)) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f702,f72])).
% 2.25/0.67  fof(f702,plain,(
% 2.25/0.67    ( ! [X0] : (~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4)) )),
% 2.25/0.67    inference(forward_demodulation,[],[f701,f536])).
% 2.25/0.67  fof(f701,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4)) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f700,f73])).
% 2.25/0.67  fof(f700,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4)) )),
% 2.25/0.67    inference(forward_demodulation,[],[f699,f536])).
% 2.25/0.67  fof(f699,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4)) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f698,f70])).
% 2.25/0.67  fof(f698,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4),sK5,X0),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK5,sK3,sK4)) )),
% 2.25/0.67    inference(resolution,[],[f514,f120])).
% 2.25/0.67  fof(f120,plain,(
% 2.25/0.67    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4)),
% 2.25/0.67    inference(backward_demodulation,[],[f78,f77])).
% 2.25/0.67  fof(f78,plain,(
% 2.25/0.67    v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | v5_pre_topc(sK5,sK3,sK4)),
% 2.25/0.67    inference(cnf_transformation,[],[f43])).
% 2.25/0.67  fof(f514,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~v5_pre_topc(sK5,X2,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK5,X0),X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2)) )),
% 2.25/0.67    inference(resolution,[],[f96,f124])).
% 2.25/0.67  fof(f96,plain,(
% 2.25/0.67    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f58])).
% 2.25/0.67  fof(f121,plain,(
% 2.25/0.67    ~v5_pre_topc(sK5,sK3,sK4) | ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4)),
% 2.25/0.67    inference(backward_demodulation,[],[f79,f77])).
% 2.25/0.67  fof(f79,plain,(
% 2.25/0.67    ~v5_pre_topc(sK6,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~v5_pre_topc(sK5,sK3,sK4)),
% 2.25/0.67    inference(cnf_transformation,[],[f43])).
% 2.25/0.67  fof(f1730,plain,(
% 2.25/0.67    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(subsumption_resolution,[],[f1729,f72])).
% 2.25/0.67  fof(f1729,plain,(
% 2.25/0.67    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(subsumption_resolution,[],[f1724,f73])).
% 2.25/0.67  fof(f1724,plain,(
% 2.25/0.67    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(resolution,[],[f1340,f755])).
% 2.25/0.67  fof(f755,plain,(
% 2.25/0.67    v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5)),sK3) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(subsumption_resolution,[],[f754,f739])).
% 2.25/0.67  fof(f739,plain,(
% 2.25/0.67    m1_subset_1(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(subsumption_resolution,[],[f458,f737])).
% 2.25/0.67  fof(f458,plain,(
% 2.25/0.67    m1_subset_1(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(subsumption_resolution,[],[f457,f70])).
% 2.25/0.67  fof(f457,plain,(
% 2.25/0.67    m1_subset_1(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(subsumption_resolution,[],[f450,f122])).
% 2.25/0.67  fof(f122,plain,(
% 2.25/0.67    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))),
% 2.25/0.67    inference(forward_demodulation,[],[f76,f77])).
% 2.25/0.67  fof(f76,plain,(
% 2.25/0.67    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))))),
% 2.25/0.67    inference(cnf_transformation,[],[f43])).
% 2.25/0.67  fof(f450,plain,(
% 2.25/0.67    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | m1_subset_1(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(resolution,[],[f448,f123])).
% 2.25/0.67  fof(f123,plain,(
% 2.25/0.67    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))),
% 2.25/0.67    inference(forward_demodulation,[],[f75,f77])).
% 2.25/0.67  fof(f75,plain,(
% 2.25/0.67    v1_funct_2(sK6,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4))),
% 2.25/0.67    inference(cnf_transformation,[],[f43])).
% 2.25/0.67  fof(f754,plain,(
% 2.25/0.67    ~m1_subset_1(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5)),sK3) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(resolution,[],[f750,f738])).
% 2.25/0.67  fof(f738,plain,(
% 2.25/0.67    v4_pre_topc(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(subsumption_resolution,[],[f433,f737])).
% 2.25/0.67  fof(f433,plain,(
% 2.25/0.67    v4_pre_topc(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(subsumption_resolution,[],[f432,f70])).
% 2.25/0.67  fof(f432,plain,(
% 2.25/0.67    v4_pre_topc(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(subsumption_resolution,[],[f428,f122])).
% 2.25/0.67  fof(f428,plain,(
% 2.25/0.67    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(sK4)))) | v4_pre_topc(sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4,sK5),sK4) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK4) | ~l1_pre_topc(sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 2.25/0.67    inference(resolution,[],[f426,f123])).
% 2.25/0.67  fof(f750,plain,(
% 2.25/0.67    ( ! [X0] : (~v4_pre_topc(X0,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3)) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f749,f68])).
% 2.25/0.67  fof(f749,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~l1_pre_topc(sK3)) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f748,f70])).
% 2.25/0.67  fof(f748,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f747,f72])).
% 2.25/0.67  fof(f747,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f746,f73])).
% 2.25/0.67  fof(f746,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) | ~v4_pre_topc(X0,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) | v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0),sK3) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK3)) )),
% 2.25/0.67    inference(resolution,[],[f736,f514])).
% 2.25/0.67  fof(f1340,plain,(
% 2.25/0.67    ( ! [X0] : (~v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(X0)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f1339,f117])).
% 2.25/0.67  fof(f1339,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(X0)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.67    inference(forward_demodulation,[],[f1338,f536])).
% 2.25/0.67  fof(f1338,plain,(
% 2.25/0.67    ( ! [X0] : (~v4_pre_topc(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(X0)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))))) )),
% 2.25/0.67    inference(forward_demodulation,[],[f1337,f536])).
% 2.25/0.67  fof(f1337,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(X0)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) | ~l1_pre_topc(X0) | ~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))))) )),
% 2.25/0.67    inference(forward_demodulation,[],[f1336,f536])).
% 2.25/0.67  fof(f1336,plain,(
% 2.25/0.67    ( ! [X0] : (~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(X0)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))))) )),
% 2.25/0.67    inference(forward_demodulation,[],[f1335,f536])).
% 2.25/0.67  fof(f1335,plain,(
% 2.25/0.67    ( ! [X0] : (~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))))) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f1329,f68])).
% 2.25/0.67  fof(f1329,plain,(
% 2.25/0.67    ( ! [X0] : (~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0),sK5,sK10(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0,sK5)),sK3) | ~l1_pre_topc(sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_struct_0(X0))))) )),
% 2.25/0.67    inference(resolution,[],[f492,f67])).
% 2.25/0.67  fof(f492,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),sK5,sK10(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1,sK5)),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),sK5,sK10(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1,sK5)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))) )),
% 2.25/0.67    inference(subsumption_resolution,[],[f491,f134])).
% 2.25/0.67  fof(f491,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),sK5,sK10(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1,sK5)),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),sK5,sK10(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1,sK5)),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.25/0.67    inference(resolution,[],[f480,f107])).
% 2.25/0.67  fof(f107,plain,(
% 2.25/0.67    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f63])).
% 2.25/0.67  % SZS output end Proof for theBenchmark
% 2.25/0.67  % (4411)------------------------------
% 2.25/0.67  % (4411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.67  % (4411)Termination reason: Refutation
% 2.25/0.67  
% 2.25/0.67  % (4411)Memory used [KB]: 7803
% 2.25/0.67  % (4411)Time elapsed: 0.240 s
% 2.25/0.67  % (4411)------------------------------
% 2.25/0.67  % (4411)------------------------------
% 2.25/0.67  % (4406)Success in time 0.31 s
%------------------------------------------------------------------------------
