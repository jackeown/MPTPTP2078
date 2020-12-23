%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:52 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  319 (80708 expanded)
%              Number of clauses        :  205 (18240 expanded)
%              Number of leaves         :   29 (23376 expanded)
%              Depth                    :   32
%              Number of atoms          : 1284 (886632 expanded)
%              Number of equality atoms :  477 (93520 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f60,f61])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f26])).

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
    inference(flattening,[],[f53])).

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
    inference(nnf_transformation,[],[f54])).

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

fof(f125,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f76])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f123,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

fof(f124,plain,(
    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f76])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f110,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f119,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f109,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f24])).

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
    inference(flattening,[],[f51])).

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
    inference(nnf_transformation,[],[f52])).

fof(f114,plain,(
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

fof(f136,plain,(
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
    inference(equality_resolution,[],[f114])).

fof(f116,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f117,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

fof(f118,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f47,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f111,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f128,plain,
    ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f126,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f76])).

fof(f127,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f121,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f76])).

fof(f122,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f76])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f23])).

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
    inference(flattening,[],[f49])).

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
    inference(nnf_transformation,[],[f50])).

fof(f113,plain,(
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

fof(f133,plain,(
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
    inference(equality_resolution,[],[f113])).

fof(f112,plain,(
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

fof(f134,plain,(
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
    inference(equality_resolution,[],[f112])).

fof(f115,plain,(
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

fof(f135,plain,(
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
    inference(equality_resolution,[],[f115])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f56,f57])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f120,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f63])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f129,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f86,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3333,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_3309,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_26,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_649,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_21,c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_26,c_21,c_19])).

cnf(c_654,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_653])).

cnf(c_759,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_23,c_654])).

cnf(c_763,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_759,c_26,c_23,c_21,c_19])).

cnf(c_764,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_763])).

cnf(c_3296,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_4287,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3309,c_3296])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_59,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_60,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_4813,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4287,c_59,c_60])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3330,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4817,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4813,c_3330])).

cnf(c_33,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_3317,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5730,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4817,c_3317])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_55,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3744,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3745,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3744])).

cnf(c_4048,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_4049,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4048])).

cnf(c_15336,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) = iProver_top
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5730,c_55,c_3745,c_4049])).

cnf(c_15337,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_15336])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3321,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6793,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3309,c_3321])).

cnf(c_7015,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4813,c_6793])).

cnf(c_8596,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7015,c_3330])).

cnf(c_38,plain,
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
    inference(cnf_transformation,[],[f136])).

cnf(c_3312,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6679,plain,
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
    inference(superposition,[status(thm)],[c_3309,c_3312])).

cnf(c_51,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_52,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_50,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_53,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_54,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_61,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_34,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_76,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_78,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_79,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_81,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_39,negated_conjecture,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3311,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_41,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_3342,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3311,c_41])).

cnf(c_40,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3)
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_3310,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3341,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3310,c_41])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3305,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_3339,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3305,c_41])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3306,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3340,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3306,c_41])).

cnf(c_3476,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3477,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3476])).

cnf(c_35,plain,
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
    inference(cnf_transformation,[],[f133])).

cnf(c_3932,plain,
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
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3938,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3932])).

cnf(c_3940,plain,
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
    inference(instantiation,[status(thm)],[c_3938])).

cnf(c_36,plain,
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
    inference(cnf_transformation,[],[f134])).

cnf(c_5375,plain,
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
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_5376,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_5375])).

cnf(c_5378,plain,
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
    inference(instantiation,[status(thm)],[c_5376])).

cnf(c_37,plain,
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
    inference(cnf_transformation,[],[f135])).

cnf(c_3933,plain,
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
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_5516,plain,
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
    inference(instantiation,[status(thm)],[c_3933])).

cnf(c_5517,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_5516])).

cnf(c_7020,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6679,c_52,c_53,c_54,c_55,c_59,c_60,c_61,c_78,c_81,c_3342,c_3341,c_3339,c_3340,c_3477,c_3940,c_5378,c_5517])).

cnf(c_7021,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7020])).

cnf(c_7024,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7021,c_52,c_53,c_54,c_55,c_59,c_60,c_61,c_78,c_81,c_3341,c_3339,c_3340,c_3477,c_5378,c_5517])).

cnf(c_10918,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8596,c_7024])).

cnf(c_3308,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_10925,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8596,c_3308])).

cnf(c_4289,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3340,c_3296])).

cnf(c_4807,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4289,c_59,c_3339])).

cnf(c_6795,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3340,c_3321])).

cnf(c_6905,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4807,c_6795])).

cnf(c_8494,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6905,c_3330])).

cnf(c_10924,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8596,c_3309])).

cnf(c_3314,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7646,plain,
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
    inference(superposition,[status(thm)],[c_3309,c_3314])).

cnf(c_3491,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_3492,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3491])).

cnf(c_3934,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3933])).

cnf(c_3936,plain,
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
    inference(instantiation,[status(thm)],[c_3934])).

cnf(c_3980,plain,
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
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_3981,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_3980])).

cnf(c_3983,plain,
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
    inference(instantiation,[status(thm)],[c_3981])).

cnf(c_3315,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7679,plain,
    ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3309,c_3315])).

cnf(c_7828,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7646,c_52,c_53,c_54,c_55,c_59,c_60,c_3342,c_3341,c_3339,c_3340,c_3492,c_3745,c_3936,c_3983,c_4049,c_7679])).

cnf(c_7829,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7828])).

cnf(c_7832,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7829,c_52,c_53,c_54,c_55,c_59,c_60,c_3341,c_3339,c_3340,c_3492,c_3745,c_3983,c_4049,c_7679])).

cnf(c_8816,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8494,c_7832])).

cnf(c_11265,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10924,c_8816])).

cnf(c_11268,plain,
    ( sK5 = k1_xboole_0
    | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8494,c_11265])).

cnf(c_11410,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10918,c_10925,c_11268])).

cnf(c_15340,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15337,c_11410])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3324,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_15342,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15340,c_3324])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3332,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16055,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15342,c_3332])).

cnf(c_19489,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0) = iProver_top
    | r2_hidden(sK1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3333,c_16055])).

cnf(c_4811,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4807,c_3330])).

cnf(c_11452,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(sK2) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_11410,c_4811])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3335,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5217,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3333,c_3335])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3325,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7836,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3325,c_7832])).

cnf(c_8967,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5217,c_7836])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_151,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2344,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6672,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_13181,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6672])).

cnf(c_13185,plain,
    ( sK5 != k1_xboole_0
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13181])).

cnf(c_15121,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8967,c_151,c_10925,c_11268,c_13185])).

cnf(c_15125,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15121,c_11410])).

cnf(c_16432,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11452,c_15125])).

cnf(c_3331,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3326,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3338,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3326,c_11])).

cnf(c_6794,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3338,c_3321])).

cnf(c_9594,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6794,c_3330])).

cnf(c_9599,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3331,c_9594])).

cnf(c_3322,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5222,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3338,c_3322])).

cnf(c_9725,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9599,c_5222])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3304,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_3337,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3304,c_41])).

cnf(c_11465,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11410,c_3337])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_13411,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_13412,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13411])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3319,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4989,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4811,c_4813])).

cnf(c_4997,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4811,c_3340])).

cnf(c_4998,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4811,c_3339])).

cnf(c_7837,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4817,c_7832])).

cnf(c_8008,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),k1_xboole_0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4817,c_7837])).

cnf(c_11720,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4989,c_4997,c_4998,c_8008])).

cnf(c_11721,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5) ),
    inference(renaming,[status(thm)],[c_11720])).

cnf(c_11722,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | u1_struct_0(sK2) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_11721,c_11410])).

cnf(c_5667,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4817,c_3309])).

cnf(c_7029,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4811,c_7024])).

cnf(c_8005,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
    | u1_struct_0(sK2) = k1_relat_1(sK5)
    | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5667,c_7029])).

cnf(c_7028,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3325,c_7024])).

cnf(c_8966,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5217,c_7028])).

cnf(c_13476,plain,
    ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8005,c_151,c_8966,c_10925,c_11268,c_13185])).

cnf(c_13480,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13476,c_11410])).

cnf(c_13482,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11722,c_13480])).

cnf(c_22426,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11452,c_13482])).

cnf(c_22567,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3319,c_22426])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3327,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_17])).

cnf(c_632,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_628,c_19])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_632])).

cnf(c_3298,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_5674,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3325,c_3298])).

cnf(c_12714,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3327,c_5674])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3329,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5925,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3327,c_3329])).

cnf(c_12872,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12714,c_5925])).

cnf(c_22568,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22567,c_12872])).

cnf(c_22571,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16432,c_9725,c_11465,c_13412,c_22568])).

cnf(c_23676,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0) = iProver_top
    | r2_hidden(sK1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19489,c_22571])).

cnf(c_11445,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_11410,c_4817])).

cnf(c_17401,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11445,c_15125])).

cnf(c_23595,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17401,c_22571])).

cnf(c_23597,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3319,c_23595])).

cnf(c_23598,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23597,c_12872])).

cnf(c_23680,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23676,c_9725,c_11465,c_13412,c_23598])).

cnf(c_22603,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22571,c_13480])).

cnf(c_23682,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23680,c_22603])).

cnf(c_11464,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11410,c_3339])).

cnf(c_22612,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22571,c_11464])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23682,c_22612])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:44:12 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.32  % Running in FOF mode
% 7.84/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/1.48  
% 7.84/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.84/1.48  
% 7.84/1.48  ------  iProver source info
% 7.84/1.48  
% 7.84/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.84/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.84/1.48  git: non_committed_changes: false
% 7.84/1.48  git: last_make_outside_of_git: false
% 7.84/1.48  
% 7.84/1.48  ------ 
% 7.84/1.48  
% 7.84/1.48  ------ Input Options
% 7.84/1.48  
% 7.84/1.48  --out_options                           all
% 7.84/1.48  --tptp_safe_out                         true
% 7.84/1.48  --problem_path                          ""
% 7.84/1.48  --include_path                          ""
% 7.84/1.48  --clausifier                            res/vclausify_rel
% 7.84/1.48  --clausifier_options                    ""
% 7.84/1.48  --stdin                                 false
% 7.84/1.48  --stats_out                             all
% 7.84/1.48  
% 7.84/1.48  ------ General Options
% 7.84/1.48  
% 7.84/1.48  --fof                                   false
% 7.84/1.48  --time_out_real                         305.
% 7.84/1.48  --time_out_virtual                      -1.
% 7.84/1.48  --symbol_type_check                     false
% 7.84/1.48  --clausify_out                          false
% 7.84/1.48  --sig_cnt_out                           false
% 7.84/1.48  --trig_cnt_out                          false
% 7.84/1.48  --trig_cnt_out_tolerance                1.
% 7.84/1.48  --trig_cnt_out_sk_spl                   false
% 7.84/1.48  --abstr_cl_out                          false
% 7.84/1.48  
% 7.84/1.48  ------ Global Options
% 7.84/1.48  
% 7.84/1.48  --schedule                              default
% 7.84/1.48  --add_important_lit                     false
% 7.84/1.48  --prop_solver_per_cl                    1000
% 7.84/1.48  --min_unsat_core                        false
% 7.84/1.48  --soft_assumptions                      false
% 7.84/1.48  --soft_lemma_size                       3
% 7.84/1.48  --prop_impl_unit_size                   0
% 7.84/1.48  --prop_impl_unit                        []
% 7.84/1.48  --share_sel_clauses                     true
% 7.84/1.48  --reset_solvers                         false
% 7.84/1.48  --bc_imp_inh                            [conj_cone]
% 7.84/1.48  --conj_cone_tolerance                   3.
% 7.84/1.48  --extra_neg_conj                        none
% 7.84/1.48  --large_theory_mode                     true
% 7.84/1.48  --prolific_symb_bound                   200
% 7.84/1.48  --lt_threshold                          2000
% 7.84/1.48  --clause_weak_htbl                      true
% 7.84/1.48  --gc_record_bc_elim                     false
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing Options
% 7.84/1.48  
% 7.84/1.48  --preprocessing_flag                    true
% 7.84/1.48  --time_out_prep_mult                    0.1
% 7.84/1.48  --splitting_mode                        input
% 7.84/1.48  --splitting_grd                         true
% 7.84/1.48  --splitting_cvd                         false
% 7.84/1.48  --splitting_cvd_svl                     false
% 7.84/1.48  --splitting_nvd                         32
% 7.84/1.48  --sub_typing                            true
% 7.84/1.48  --prep_gs_sim                           true
% 7.84/1.48  --prep_unflatten                        true
% 7.84/1.48  --prep_res_sim                          true
% 7.84/1.48  --prep_upred                            true
% 7.84/1.48  --prep_sem_filter                       exhaustive
% 7.84/1.48  --prep_sem_filter_out                   false
% 7.84/1.48  --pred_elim                             true
% 7.84/1.48  --res_sim_input                         true
% 7.84/1.48  --eq_ax_congr_red                       true
% 7.84/1.48  --pure_diseq_elim                       true
% 7.84/1.48  --brand_transform                       false
% 7.84/1.48  --non_eq_to_eq                          false
% 7.84/1.48  --prep_def_merge                        true
% 7.84/1.48  --prep_def_merge_prop_impl              false
% 7.84/1.48  --prep_def_merge_mbd                    true
% 7.84/1.48  --prep_def_merge_tr_red                 false
% 7.84/1.48  --prep_def_merge_tr_cl                  false
% 7.84/1.48  --smt_preprocessing                     true
% 7.84/1.48  --smt_ac_axioms                         fast
% 7.84/1.48  --preprocessed_out                      false
% 7.84/1.48  --preprocessed_stats                    false
% 7.84/1.48  
% 7.84/1.48  ------ Abstraction refinement Options
% 7.84/1.48  
% 7.84/1.48  --abstr_ref                             []
% 7.84/1.48  --abstr_ref_prep                        false
% 7.84/1.48  --abstr_ref_until_sat                   false
% 7.84/1.48  --abstr_ref_sig_restrict                funpre
% 7.84/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.84/1.48  --abstr_ref_under                       []
% 7.84/1.48  
% 7.84/1.48  ------ SAT Options
% 7.84/1.48  
% 7.84/1.48  --sat_mode                              false
% 7.84/1.48  --sat_fm_restart_options                ""
% 7.84/1.48  --sat_gr_def                            false
% 7.84/1.48  --sat_epr_types                         true
% 7.84/1.48  --sat_non_cyclic_types                  false
% 7.84/1.48  --sat_finite_models                     false
% 7.84/1.48  --sat_fm_lemmas                         false
% 7.84/1.48  --sat_fm_prep                           false
% 7.84/1.48  --sat_fm_uc_incr                        true
% 7.84/1.48  --sat_out_model                         small
% 7.84/1.48  --sat_out_clauses                       false
% 7.84/1.48  
% 7.84/1.48  ------ QBF Options
% 7.84/1.48  
% 7.84/1.48  --qbf_mode                              false
% 7.84/1.48  --qbf_elim_univ                         false
% 7.84/1.48  --qbf_dom_inst                          none
% 7.84/1.48  --qbf_dom_pre_inst                      false
% 7.84/1.48  --qbf_sk_in                             false
% 7.84/1.48  --qbf_pred_elim                         true
% 7.84/1.48  --qbf_split                             512
% 7.84/1.48  
% 7.84/1.48  ------ BMC1 Options
% 7.84/1.48  
% 7.84/1.48  --bmc1_incremental                      false
% 7.84/1.48  --bmc1_axioms                           reachable_all
% 7.84/1.48  --bmc1_min_bound                        0
% 7.84/1.48  --bmc1_max_bound                        -1
% 7.84/1.48  --bmc1_max_bound_default                -1
% 7.84/1.48  --bmc1_symbol_reachability              true
% 7.84/1.48  --bmc1_property_lemmas                  false
% 7.84/1.48  --bmc1_k_induction                      false
% 7.84/1.48  --bmc1_non_equiv_states                 false
% 7.84/1.48  --bmc1_deadlock                         false
% 7.84/1.48  --bmc1_ucm                              false
% 7.84/1.48  --bmc1_add_unsat_core                   none
% 7.84/1.48  --bmc1_unsat_core_children              false
% 7.84/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.84/1.48  --bmc1_out_stat                         full
% 7.84/1.48  --bmc1_ground_init                      false
% 7.84/1.48  --bmc1_pre_inst_next_state              false
% 7.84/1.48  --bmc1_pre_inst_state                   false
% 7.84/1.48  --bmc1_pre_inst_reach_state             false
% 7.84/1.48  --bmc1_out_unsat_core                   false
% 7.84/1.48  --bmc1_aig_witness_out                  false
% 7.84/1.48  --bmc1_verbose                          false
% 7.84/1.48  --bmc1_dump_clauses_tptp                false
% 7.84/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.84/1.48  --bmc1_dump_file                        -
% 7.84/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.84/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.84/1.48  --bmc1_ucm_extend_mode                  1
% 7.84/1.48  --bmc1_ucm_init_mode                    2
% 7.84/1.48  --bmc1_ucm_cone_mode                    none
% 7.84/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.84/1.48  --bmc1_ucm_relax_model                  4
% 7.84/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.84/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.84/1.48  --bmc1_ucm_layered_model                none
% 7.84/1.48  --bmc1_ucm_max_lemma_size               10
% 7.84/1.48  
% 7.84/1.48  ------ AIG Options
% 7.84/1.48  
% 7.84/1.48  --aig_mode                              false
% 7.84/1.48  
% 7.84/1.48  ------ Instantiation Options
% 7.84/1.48  
% 7.84/1.48  --instantiation_flag                    true
% 7.84/1.48  --inst_sos_flag                         true
% 7.84/1.48  --inst_sos_phase                        true
% 7.84/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.84/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.84/1.48  --inst_lit_sel_side                     num_symb
% 7.84/1.48  --inst_solver_per_active                1400
% 7.84/1.48  --inst_solver_calls_frac                1.
% 7.84/1.48  --inst_passive_queue_type               priority_queues
% 7.84/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.84/1.48  --inst_passive_queues_freq              [25;2]
% 7.84/1.48  --inst_dismatching                      true
% 7.84/1.48  --inst_eager_unprocessed_to_passive     true
% 7.84/1.48  --inst_prop_sim_given                   true
% 7.84/1.48  --inst_prop_sim_new                     false
% 7.84/1.48  --inst_subs_new                         false
% 7.84/1.48  --inst_eq_res_simp                      false
% 7.84/1.48  --inst_subs_given                       false
% 7.84/1.48  --inst_orphan_elimination               true
% 7.84/1.48  --inst_learning_loop_flag               true
% 7.84/1.48  --inst_learning_start                   3000
% 7.84/1.48  --inst_learning_factor                  2
% 7.84/1.48  --inst_start_prop_sim_after_learn       3
% 7.84/1.48  --inst_sel_renew                        solver
% 7.84/1.48  --inst_lit_activity_flag                true
% 7.84/1.48  --inst_restr_to_given                   false
% 7.84/1.48  --inst_activity_threshold               500
% 7.84/1.48  --inst_out_proof                        true
% 7.84/1.48  
% 7.84/1.48  ------ Resolution Options
% 7.84/1.48  
% 7.84/1.48  --resolution_flag                       true
% 7.84/1.48  --res_lit_sel                           adaptive
% 7.84/1.48  --res_lit_sel_side                      none
% 7.84/1.48  --res_ordering                          kbo
% 7.84/1.48  --res_to_prop_solver                    active
% 7.84/1.48  --res_prop_simpl_new                    false
% 7.84/1.48  --res_prop_simpl_given                  true
% 7.84/1.48  --res_passive_queue_type                priority_queues
% 7.84/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.84/1.48  --res_passive_queues_freq               [15;5]
% 7.84/1.48  --res_forward_subs                      full
% 7.84/1.48  --res_backward_subs                     full
% 7.84/1.48  --res_forward_subs_resolution           true
% 7.84/1.48  --res_backward_subs_resolution          true
% 7.84/1.48  --res_orphan_elimination                true
% 7.84/1.48  --res_time_limit                        2.
% 7.84/1.48  --res_out_proof                         true
% 7.84/1.48  
% 7.84/1.48  ------ Superposition Options
% 7.84/1.48  
% 7.84/1.48  --superposition_flag                    true
% 7.84/1.48  --sup_passive_queue_type                priority_queues
% 7.84/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.84/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.84/1.48  --demod_completeness_check              fast
% 7.84/1.48  --demod_use_ground                      true
% 7.84/1.48  --sup_to_prop_solver                    passive
% 7.84/1.48  --sup_prop_simpl_new                    true
% 7.84/1.48  --sup_prop_simpl_given                  true
% 7.84/1.48  --sup_fun_splitting                     true
% 7.84/1.48  --sup_smt_interval                      50000
% 7.84/1.48  
% 7.84/1.48  ------ Superposition Simplification Setup
% 7.84/1.48  
% 7.84/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.84/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.84/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.84/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.84/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.84/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.84/1.48  --sup_immed_triv                        [TrivRules]
% 7.84/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_immed_bw_main                     []
% 7.84/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.84/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.84/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_input_bw                          []
% 7.84/1.48  
% 7.84/1.48  ------ Combination Options
% 7.84/1.48  
% 7.84/1.48  --comb_res_mult                         3
% 7.84/1.48  --comb_sup_mult                         2
% 7.84/1.48  --comb_inst_mult                        10
% 7.84/1.48  
% 7.84/1.48  ------ Debug Options
% 7.84/1.48  
% 7.84/1.48  --dbg_backtrace                         false
% 7.84/1.48  --dbg_dump_prop_clauses                 false
% 7.84/1.48  --dbg_dump_prop_clauses_file            -
% 7.84/1.48  --dbg_out_stat                          false
% 7.84/1.48  ------ Parsing...
% 7.84/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.84/1.48  ------ Proving...
% 7.84/1.48  ------ Problem Properties 
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  clauses                                 44
% 7.84/1.48  conjectures                             13
% 7.84/1.48  EPR                                     16
% 7.84/1.48  Horn                                    39
% 7.84/1.48  unary                                   16
% 7.84/1.48  binary                                  14
% 7.84/1.48  lits                                    126
% 7.84/1.48  lits eq                                 8
% 7.84/1.48  fd_pure                                 0
% 7.84/1.48  fd_pseudo                               0
% 7.84/1.48  fd_cond                                 1
% 7.84/1.48  fd_pseudo_cond                          3
% 7.84/1.48  AC symbols                              0
% 7.84/1.48  
% 7.84/1.48  ------ Schedule dynamic 5 is on 
% 7.84/1.48  
% 7.84/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  ------ 
% 7.84/1.48  Current options:
% 7.84/1.48  ------ 
% 7.84/1.48  
% 7.84/1.48  ------ Input Options
% 7.84/1.48  
% 7.84/1.48  --out_options                           all
% 7.84/1.48  --tptp_safe_out                         true
% 7.84/1.48  --problem_path                          ""
% 7.84/1.48  --include_path                          ""
% 7.84/1.48  --clausifier                            res/vclausify_rel
% 7.84/1.48  --clausifier_options                    ""
% 7.84/1.48  --stdin                                 false
% 7.84/1.48  --stats_out                             all
% 7.84/1.48  
% 7.84/1.48  ------ General Options
% 7.84/1.48  
% 7.84/1.48  --fof                                   false
% 7.84/1.48  --time_out_real                         305.
% 7.84/1.48  --time_out_virtual                      -1.
% 7.84/1.48  --symbol_type_check                     false
% 7.84/1.48  --clausify_out                          false
% 7.84/1.48  --sig_cnt_out                           false
% 7.84/1.48  --trig_cnt_out                          false
% 7.84/1.48  --trig_cnt_out_tolerance                1.
% 7.84/1.48  --trig_cnt_out_sk_spl                   false
% 7.84/1.48  --abstr_cl_out                          false
% 7.84/1.48  
% 7.84/1.48  ------ Global Options
% 7.84/1.48  
% 7.84/1.48  --schedule                              default
% 7.84/1.48  --add_important_lit                     false
% 7.84/1.48  --prop_solver_per_cl                    1000
% 7.84/1.48  --min_unsat_core                        false
% 7.84/1.48  --soft_assumptions                      false
% 7.84/1.48  --soft_lemma_size                       3
% 7.84/1.48  --prop_impl_unit_size                   0
% 7.84/1.48  --prop_impl_unit                        []
% 7.84/1.48  --share_sel_clauses                     true
% 7.84/1.48  --reset_solvers                         false
% 7.84/1.48  --bc_imp_inh                            [conj_cone]
% 7.84/1.48  --conj_cone_tolerance                   3.
% 7.84/1.48  --extra_neg_conj                        none
% 7.84/1.48  --large_theory_mode                     true
% 7.84/1.48  --prolific_symb_bound                   200
% 7.84/1.48  --lt_threshold                          2000
% 7.84/1.48  --clause_weak_htbl                      true
% 7.84/1.48  --gc_record_bc_elim                     false
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing Options
% 7.84/1.48  
% 7.84/1.48  --preprocessing_flag                    true
% 7.84/1.48  --time_out_prep_mult                    0.1
% 7.84/1.48  --splitting_mode                        input
% 7.84/1.48  --splitting_grd                         true
% 7.84/1.48  --splitting_cvd                         false
% 7.84/1.48  --splitting_cvd_svl                     false
% 7.84/1.48  --splitting_nvd                         32
% 7.84/1.48  --sub_typing                            true
% 7.84/1.48  --prep_gs_sim                           true
% 7.84/1.48  --prep_unflatten                        true
% 7.84/1.48  --prep_res_sim                          true
% 7.84/1.48  --prep_upred                            true
% 7.84/1.48  --prep_sem_filter                       exhaustive
% 7.84/1.48  --prep_sem_filter_out                   false
% 7.84/1.48  --pred_elim                             true
% 7.84/1.48  --res_sim_input                         true
% 7.84/1.48  --eq_ax_congr_red                       true
% 7.84/1.48  --pure_diseq_elim                       true
% 7.84/1.48  --brand_transform                       false
% 7.84/1.48  --non_eq_to_eq                          false
% 7.84/1.48  --prep_def_merge                        true
% 7.84/1.48  --prep_def_merge_prop_impl              false
% 7.84/1.48  --prep_def_merge_mbd                    true
% 7.84/1.48  --prep_def_merge_tr_red                 false
% 7.84/1.48  --prep_def_merge_tr_cl                  false
% 7.84/1.48  --smt_preprocessing                     true
% 7.84/1.48  --smt_ac_axioms                         fast
% 7.84/1.48  --preprocessed_out                      false
% 7.84/1.48  --preprocessed_stats                    false
% 7.84/1.48  
% 7.84/1.48  ------ Abstraction refinement Options
% 7.84/1.48  
% 7.84/1.48  --abstr_ref                             []
% 7.84/1.48  --abstr_ref_prep                        false
% 7.84/1.48  --abstr_ref_until_sat                   false
% 7.84/1.48  --abstr_ref_sig_restrict                funpre
% 7.84/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.84/1.48  --abstr_ref_under                       []
% 7.84/1.48  
% 7.84/1.48  ------ SAT Options
% 7.84/1.48  
% 7.84/1.48  --sat_mode                              false
% 7.84/1.48  --sat_fm_restart_options                ""
% 7.84/1.48  --sat_gr_def                            false
% 7.84/1.48  --sat_epr_types                         true
% 7.84/1.48  --sat_non_cyclic_types                  false
% 7.84/1.48  --sat_finite_models                     false
% 7.84/1.48  --sat_fm_lemmas                         false
% 7.84/1.48  --sat_fm_prep                           false
% 7.84/1.48  --sat_fm_uc_incr                        true
% 7.84/1.48  --sat_out_model                         small
% 7.84/1.48  --sat_out_clauses                       false
% 7.84/1.48  
% 7.84/1.48  ------ QBF Options
% 7.84/1.48  
% 7.84/1.48  --qbf_mode                              false
% 7.84/1.48  --qbf_elim_univ                         false
% 7.84/1.48  --qbf_dom_inst                          none
% 7.84/1.48  --qbf_dom_pre_inst                      false
% 7.84/1.48  --qbf_sk_in                             false
% 7.84/1.48  --qbf_pred_elim                         true
% 7.84/1.48  --qbf_split                             512
% 7.84/1.48  
% 7.84/1.48  ------ BMC1 Options
% 7.84/1.48  
% 7.84/1.48  --bmc1_incremental                      false
% 7.84/1.48  --bmc1_axioms                           reachable_all
% 7.84/1.48  --bmc1_min_bound                        0
% 7.84/1.48  --bmc1_max_bound                        -1
% 7.84/1.48  --bmc1_max_bound_default                -1
% 7.84/1.48  --bmc1_symbol_reachability              true
% 7.84/1.48  --bmc1_property_lemmas                  false
% 7.84/1.48  --bmc1_k_induction                      false
% 7.84/1.48  --bmc1_non_equiv_states                 false
% 7.84/1.48  --bmc1_deadlock                         false
% 7.84/1.48  --bmc1_ucm                              false
% 7.84/1.48  --bmc1_add_unsat_core                   none
% 7.84/1.48  --bmc1_unsat_core_children              false
% 7.84/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.84/1.48  --bmc1_out_stat                         full
% 7.84/1.48  --bmc1_ground_init                      false
% 7.84/1.48  --bmc1_pre_inst_next_state              false
% 7.84/1.48  --bmc1_pre_inst_state                   false
% 7.84/1.48  --bmc1_pre_inst_reach_state             false
% 7.84/1.48  --bmc1_out_unsat_core                   false
% 7.84/1.48  --bmc1_aig_witness_out                  false
% 7.84/1.48  --bmc1_verbose                          false
% 7.84/1.48  --bmc1_dump_clauses_tptp                false
% 7.84/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.84/1.48  --bmc1_dump_file                        -
% 7.84/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.84/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.84/1.48  --bmc1_ucm_extend_mode                  1
% 7.84/1.48  --bmc1_ucm_init_mode                    2
% 7.84/1.48  --bmc1_ucm_cone_mode                    none
% 7.84/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.84/1.48  --bmc1_ucm_relax_model                  4
% 7.84/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.84/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.84/1.48  --bmc1_ucm_layered_model                none
% 7.84/1.48  --bmc1_ucm_max_lemma_size               10
% 7.84/1.48  
% 7.84/1.48  ------ AIG Options
% 7.84/1.48  
% 7.84/1.48  --aig_mode                              false
% 7.84/1.48  
% 7.84/1.48  ------ Instantiation Options
% 7.84/1.48  
% 7.84/1.48  --instantiation_flag                    true
% 7.84/1.48  --inst_sos_flag                         true
% 7.84/1.48  --inst_sos_phase                        true
% 7.84/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.84/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.84/1.48  --inst_lit_sel_side                     none
% 7.84/1.48  --inst_solver_per_active                1400
% 7.84/1.48  --inst_solver_calls_frac                1.
% 7.84/1.48  --inst_passive_queue_type               priority_queues
% 7.84/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.84/1.48  --inst_passive_queues_freq              [25;2]
% 7.84/1.48  --inst_dismatching                      true
% 7.84/1.48  --inst_eager_unprocessed_to_passive     true
% 7.84/1.48  --inst_prop_sim_given                   true
% 7.84/1.48  --inst_prop_sim_new                     false
% 7.84/1.48  --inst_subs_new                         false
% 7.84/1.48  --inst_eq_res_simp                      false
% 7.84/1.48  --inst_subs_given                       false
% 7.84/1.48  --inst_orphan_elimination               true
% 7.84/1.48  --inst_learning_loop_flag               true
% 7.84/1.48  --inst_learning_start                   3000
% 7.84/1.48  --inst_learning_factor                  2
% 7.84/1.48  --inst_start_prop_sim_after_learn       3
% 7.84/1.48  --inst_sel_renew                        solver
% 7.84/1.48  --inst_lit_activity_flag                true
% 7.84/1.48  --inst_restr_to_given                   false
% 7.84/1.48  --inst_activity_threshold               500
% 7.84/1.48  --inst_out_proof                        true
% 7.84/1.48  
% 7.84/1.48  ------ Resolution Options
% 7.84/1.48  
% 7.84/1.48  --resolution_flag                       false
% 7.84/1.48  --res_lit_sel                           adaptive
% 7.84/1.48  --res_lit_sel_side                      none
% 7.84/1.48  --res_ordering                          kbo
% 7.84/1.48  --res_to_prop_solver                    active
% 7.84/1.48  --res_prop_simpl_new                    false
% 7.84/1.48  --res_prop_simpl_given                  true
% 7.84/1.48  --res_passive_queue_type                priority_queues
% 7.84/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.84/1.48  --res_passive_queues_freq               [15;5]
% 7.84/1.48  --res_forward_subs                      full
% 7.84/1.48  --res_backward_subs                     full
% 7.84/1.48  --res_forward_subs_resolution           true
% 7.84/1.48  --res_backward_subs_resolution          true
% 7.84/1.48  --res_orphan_elimination                true
% 7.84/1.48  --res_time_limit                        2.
% 7.84/1.48  --res_out_proof                         true
% 7.84/1.48  
% 7.84/1.48  ------ Superposition Options
% 7.84/1.48  
% 7.84/1.48  --superposition_flag                    true
% 7.84/1.48  --sup_passive_queue_type                priority_queues
% 7.84/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.84/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.84/1.48  --demod_completeness_check              fast
% 7.84/1.48  --demod_use_ground                      true
% 7.84/1.48  --sup_to_prop_solver                    passive
% 7.84/1.48  --sup_prop_simpl_new                    true
% 7.84/1.48  --sup_prop_simpl_given                  true
% 7.84/1.48  --sup_fun_splitting                     true
% 7.84/1.48  --sup_smt_interval                      50000
% 7.84/1.48  
% 7.84/1.48  ------ Superposition Simplification Setup
% 7.84/1.48  
% 7.84/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.84/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.84/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.84/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.84/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.84/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.84/1.48  --sup_immed_triv                        [TrivRules]
% 7.84/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_immed_bw_main                     []
% 7.84/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.84/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.84/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_input_bw                          []
% 7.84/1.48  
% 7.84/1.48  ------ Combination Options
% 7.84/1.48  
% 7.84/1.48  --comb_res_mult                         3
% 7.84/1.48  --comb_sup_mult                         2
% 7.84/1.48  --comb_inst_mult                        10
% 7.84/1.48  
% 7.84/1.48  ------ Debug Options
% 7.84/1.48  
% 7.84/1.48  --dbg_backtrace                         false
% 7.84/1.48  --dbg_dump_prop_clauses                 false
% 7.84/1.48  --dbg_dump_prop_clauses_file            -
% 7.84/1.48  --dbg_out_stat                          false
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  ------ Proving...
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  % SZS status Theorem for theBenchmark.p
% 7.84/1.48  
% 7.84/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.84/1.48  
% 7.84/1.48  fof(f2,axiom,(
% 7.84/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.84/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f29,plain,(
% 7.84/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.84/1.48    inference(ennf_transformation,[],[f2])).
% 7.84/1.48  
% 7.84/1.48  fof(f59,plain,(
% 7.84/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.84/1.48    inference(nnf_transformation,[],[f29])).
% 7.84/1.48  
% 7.84/1.48  fof(f60,plain,(
% 7.84/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.84/1.48    inference(rectify,[],[f59])).
% 7.84/1.48  
% 7.84/1.48  fof(f61,plain,(
% 7.84/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.84/1.48    introduced(choice_axiom,[])).
% 7.84/1.48  
% 7.84/1.48  fof(f62,plain,(
% 7.84/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.84/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f60,f61])).
% 7.84/1.48  
% 7.84/1.48  fof(f80,plain,(
% 7.84/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f62])).
% 7.84/1.48  
% 7.84/1.48  fof(f25,conjecture,(
% 7.84/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f26,negated_conjecture,(
% 7.84/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.84/1.49    inference(negated_conjecture,[],[f25])).
% 7.84/1.49  
% 7.84/1.49  fof(f53,plain,(
% 7.84/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.84/1.49    inference(ennf_transformation,[],[f26])).
% 7.84/1.49  
% 7.84/1.49  fof(f54,plain,(
% 7.84/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.84/1.49    inference(flattening,[],[f53])).
% 7.84/1.49  
% 7.84/1.49  fof(f70,plain,(
% 7.84/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.84/1.49    inference(nnf_transformation,[],[f54])).
% 7.84/1.49  
% 7.84/1.49  fof(f71,plain,(
% 7.84/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.84/1.49    inference(flattening,[],[f70])).
% 7.84/1.49  
% 7.84/1.49  fof(f75,plain,(
% 7.84/1.49    ( ! [X2,X0,X1] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & sK5 = X2 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(sK5))) )),
% 7.84/1.49    introduced(choice_axiom,[])).
% 7.84/1.49  
% 7.84/1.49  fof(f74,plain,(
% 7.84/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(sK4,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(sK4,X0,X1)) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.84/1.49    introduced(choice_axiom,[])).
% 7.84/1.49  
% 7.84/1.49  fof(f73,plain,(
% 7.84/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(X2,X0,sK3)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(X2,X0,sK3)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))) )),
% 7.84/1.49    introduced(choice_axiom,[])).
% 7.84/1.49  
% 7.84/1.49  fof(f72,plain,(
% 7.84/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK2,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK2,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 7.84/1.49    introduced(choice_axiom,[])).
% 7.84/1.49  
% 7.84/1.49  fof(f76,plain,(
% 7.84/1.49    ((((~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)) & (v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)) & sK4 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) & v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 7.84/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f71,f75,f74,f73,f72])).
% 7.84/1.49  
% 7.84/1.49  fof(f125,plain,(
% 7.84/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f16,axiom,(
% 7.84/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f37,plain,(
% 7.84/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.84/1.49    inference(ennf_transformation,[],[f16])).
% 7.84/1.49  
% 7.84/1.49  fof(f38,plain,(
% 7.84/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.84/1.49    inference(flattening,[],[f37])).
% 7.84/1.49  
% 7.84/1.49  fof(f101,plain,(
% 7.84/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f38])).
% 7.84/1.49  
% 7.84/1.49  fof(f14,axiom,(
% 7.84/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f35,plain,(
% 7.84/1.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.84/1.49    inference(ennf_transformation,[],[f14])).
% 7.84/1.49  
% 7.84/1.49  fof(f97,plain,(
% 7.84/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.84/1.49    inference(cnf_transformation,[],[f35])).
% 7.84/1.49  
% 7.84/1.49  fof(f17,axiom,(
% 7.84/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f39,plain,(
% 7.84/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.84/1.49    inference(ennf_transformation,[],[f17])).
% 7.84/1.49  
% 7.84/1.49  fof(f40,plain,(
% 7.84/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.84/1.49    inference(flattening,[],[f39])).
% 7.84/1.49  
% 7.84/1.49  fof(f67,plain,(
% 7.84/1.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.84/1.49    inference(nnf_transformation,[],[f40])).
% 7.84/1.49  
% 7.84/1.49  fof(f102,plain,(
% 7.84/1.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f67])).
% 7.84/1.49  
% 7.84/1.49  fof(f13,axiom,(
% 7.84/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f34,plain,(
% 7.84/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.84/1.49    inference(ennf_transformation,[],[f13])).
% 7.84/1.49  
% 7.84/1.49  fof(f96,plain,(
% 7.84/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.84/1.49    inference(cnf_transformation,[],[f34])).
% 7.84/1.49  
% 7.84/1.49  fof(f123,plain,(
% 7.84/1.49    v1_funct_1(sK5)),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f124,plain,(
% 7.84/1.49    v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f4,axiom,(
% 7.84/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f30,plain,(
% 7.84/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.84/1.49    inference(ennf_transformation,[],[f4])).
% 7.84/1.49  
% 7.84/1.49  fof(f83,plain,(
% 7.84/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f30])).
% 7.84/1.49  
% 7.84/1.49  fof(f21,axiom,(
% 7.84/1.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f46,plain,(
% 7.84/1.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.84/1.49    inference(ennf_transformation,[],[f21])).
% 7.84/1.49  
% 7.84/1.49  fof(f110,plain,(
% 7.84/1.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f46])).
% 7.84/1.49  
% 7.84/1.49  fof(f119,plain,(
% 7.84/1.49    l1_pre_topc(sK3)),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f20,axiom,(
% 7.84/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f28,plain,(
% 7.84/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.84/1.49    inference(pure_predicate_removal,[],[f20])).
% 7.84/1.49  
% 7.84/1.49  fof(f45,plain,(
% 7.84/1.49    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.84/1.49    inference(ennf_transformation,[],[f28])).
% 7.84/1.49  
% 7.84/1.49  fof(f109,plain,(
% 7.84/1.49    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.84/1.49    inference(cnf_transformation,[],[f45])).
% 7.84/1.49  
% 7.84/1.49  fof(f15,axiom,(
% 7.84/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f36,plain,(
% 7.84/1.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.84/1.49    inference(ennf_transformation,[],[f15])).
% 7.84/1.49  
% 7.84/1.49  fof(f99,plain,(
% 7.84/1.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f36])).
% 7.84/1.49  
% 7.84/1.49  fof(f24,axiom,(
% 7.84/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f51,plain,(
% 7.84/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.84/1.49    inference(ennf_transformation,[],[f24])).
% 7.84/1.49  
% 7.84/1.49  fof(f52,plain,(
% 7.84/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.84/1.49    inference(flattening,[],[f51])).
% 7.84/1.49  
% 7.84/1.49  fof(f69,plain,(
% 7.84/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.84/1.49    inference(nnf_transformation,[],[f52])).
% 7.84/1.49  
% 7.84/1.49  fof(f114,plain,(
% 7.84/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f69])).
% 7.84/1.49  
% 7.84/1.49  fof(f136,plain,(
% 7.84/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.84/1.49    inference(equality_resolution,[],[f114])).
% 7.84/1.49  
% 7.84/1.49  fof(f116,plain,(
% 7.84/1.49    v2_pre_topc(sK2)),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f117,plain,(
% 7.84/1.49    l1_pre_topc(sK2)),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f118,plain,(
% 7.84/1.49    v2_pre_topc(sK3)),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f22,axiom,(
% 7.84/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f27,plain,(
% 7.84/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.84/1.49    inference(pure_predicate_removal,[],[f22])).
% 7.84/1.49  
% 7.84/1.49  fof(f47,plain,(
% 7.84/1.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.84/1.49    inference(ennf_transformation,[],[f27])).
% 7.84/1.49  
% 7.84/1.49  fof(f48,plain,(
% 7.84/1.49    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.84/1.49    inference(flattening,[],[f47])).
% 7.84/1.49  
% 7.84/1.49  fof(f111,plain,(
% 7.84/1.49    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f48])).
% 7.84/1.49  
% 7.84/1.49  fof(f128,plain,(
% 7.84/1.49    ~v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~v5_pre_topc(sK4,sK2,sK3)),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f126,plain,(
% 7.84/1.49    sK4 = sK5),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f127,plain,(
% 7.84/1.49    v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | v5_pre_topc(sK4,sK2,sK3)),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f121,plain,(
% 7.84/1.49    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f122,plain,(
% 7.84/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f23,axiom,(
% 7.84/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f49,plain,(
% 7.84/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.84/1.49    inference(ennf_transformation,[],[f23])).
% 7.84/1.49  
% 7.84/1.49  fof(f50,plain,(
% 7.84/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.84/1.49    inference(flattening,[],[f49])).
% 7.84/1.49  
% 7.84/1.49  fof(f68,plain,(
% 7.84/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.84/1.49    inference(nnf_transformation,[],[f50])).
% 7.84/1.49  
% 7.84/1.49  fof(f113,plain,(
% 7.84/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f68])).
% 7.84/1.49  
% 7.84/1.49  fof(f133,plain,(
% 7.84/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.84/1.49    inference(equality_resolution,[],[f113])).
% 7.84/1.49  
% 7.84/1.49  fof(f112,plain,(
% 7.84/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f68])).
% 7.84/1.49  
% 7.84/1.49  fof(f134,plain,(
% 7.84/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.84/1.49    inference(equality_resolution,[],[f112])).
% 7.84/1.49  
% 7.84/1.49  fof(f115,plain,(
% 7.84/1.49    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f69])).
% 7.84/1.49  
% 7.84/1.49  fof(f135,plain,(
% 7.84/1.49    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.84/1.49    inference(equality_resolution,[],[f115])).
% 7.84/1.49  
% 7.84/1.49  fof(f10,axiom,(
% 7.84/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f65,plain,(
% 7.84/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.84/1.49    inference(nnf_transformation,[],[f10])).
% 7.84/1.49  
% 7.84/1.49  fof(f91,plain,(
% 7.84/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.84/1.49    inference(cnf_transformation,[],[f65])).
% 7.84/1.49  
% 7.84/1.49  fof(f79,plain,(
% 7.84/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f62])).
% 7.84/1.49  
% 7.84/1.49  fof(f1,axiom,(
% 7.84/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f55,plain,(
% 7.84/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.84/1.49    inference(nnf_transformation,[],[f1])).
% 7.84/1.49  
% 7.84/1.49  fof(f56,plain,(
% 7.84/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.84/1.49    inference(rectify,[],[f55])).
% 7.84/1.49  
% 7.84/1.49  fof(f57,plain,(
% 7.84/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.84/1.49    introduced(choice_axiom,[])).
% 7.84/1.49  
% 7.84/1.49  fof(f58,plain,(
% 7.84/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.84/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f56,f57])).
% 7.84/1.49  
% 7.84/1.49  fof(f77,plain,(
% 7.84/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f58])).
% 7.84/1.49  
% 7.84/1.49  fof(f92,plain,(
% 7.84/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f65])).
% 7.84/1.49  
% 7.84/1.49  fof(f3,axiom,(
% 7.84/1.49    v1_xboole_0(k1_xboole_0)),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f82,plain,(
% 7.84/1.49    v1_xboole_0(k1_xboole_0)),
% 7.84/1.49    inference(cnf_transformation,[],[f3])).
% 7.84/1.49  
% 7.84/1.49  fof(f8,axiom,(
% 7.84/1.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f89,plain,(
% 7.84/1.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.84/1.49    inference(cnf_transformation,[],[f8])).
% 7.84/1.49  
% 7.84/1.49  fof(f7,axiom,(
% 7.84/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f88,plain,(
% 7.84/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.84/1.49    inference(cnf_transformation,[],[f7])).
% 7.84/1.49  
% 7.84/1.49  fof(f120,plain,(
% 7.84/1.49    v1_funct_1(sK4)),
% 7.84/1.49    inference(cnf_transformation,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f5,axiom,(
% 7.84/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f63,plain,(
% 7.84/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.84/1.49    inference(nnf_transformation,[],[f5])).
% 7.84/1.49  
% 7.84/1.49  fof(f64,plain,(
% 7.84/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.84/1.49    inference(flattening,[],[f63])).
% 7.84/1.49  
% 7.84/1.49  fof(f85,plain,(
% 7.84/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.84/1.49    inference(cnf_transformation,[],[f64])).
% 7.84/1.49  
% 7.84/1.49  fof(f129,plain,(
% 7.84/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.84/1.49    inference(equality_resolution,[],[f85])).
% 7.84/1.49  
% 7.84/1.49  fof(f19,axiom,(
% 7.84/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f43,plain,(
% 7.84/1.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.84/1.49    inference(ennf_transformation,[],[f19])).
% 7.84/1.49  
% 7.84/1.49  fof(f44,plain,(
% 7.84/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.84/1.49    inference(flattening,[],[f43])).
% 7.84/1.49  
% 7.84/1.49  fof(f107,plain,(
% 7.84/1.49    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f44])).
% 7.84/1.49  
% 7.84/1.49  fof(f6,axiom,(
% 7.84/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f87,plain,(
% 7.84/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f6])).
% 7.84/1.49  
% 7.84/1.49  fof(f98,plain,(
% 7.84/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.84/1.49    inference(cnf_transformation,[],[f35])).
% 7.84/1.49  
% 7.84/1.49  fof(f11,axiom,(
% 7.84/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.84/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f32,plain,(
% 7.84/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.84/1.49    inference(ennf_transformation,[],[f11])).
% 7.84/1.49  
% 7.84/1.49  fof(f66,plain,(
% 7.84/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.84/1.49    inference(nnf_transformation,[],[f32])).
% 7.84/1.49  
% 7.84/1.49  fof(f93,plain,(
% 7.84/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f66])).
% 7.84/1.49  
% 7.84/1.49  fof(f86,plain,(
% 7.84/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.84/1.49    inference(cnf_transformation,[],[f64])).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3,plain,
% 7.84/1.49      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3333,plain,
% 7.84/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.84/1.49      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_42,negated_conjecture,
% 7.84/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
% 7.84/1.49      inference(cnf_transformation,[],[f125]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3309,plain,
% 7.84/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_23,plain,
% 7.84/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.84/1.49      | v1_partfun1(X0,X1)
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | ~ v1_funct_1(X0)
% 7.84/1.49      | v1_xboole_0(X2) ),
% 7.84/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_21,plain,
% 7.84/1.49      ( v4_relat_1(X0,X1)
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.84/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_26,plain,
% 7.84/1.49      ( ~ v1_partfun1(X0,X1)
% 7.84/1.49      | ~ v4_relat_1(X0,X1)
% 7.84/1.49      | ~ v1_relat_1(X0)
% 7.84/1.49      | k1_relat_1(X0) = X1 ),
% 7.84/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_649,plain,
% 7.84/1.49      ( ~ v1_partfun1(X0,X1)
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | ~ v1_relat_1(X0)
% 7.84/1.49      | k1_relat_1(X0) = X1 ),
% 7.84/1.49      inference(resolution,[status(thm)],[c_21,c_26]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_19,plain,
% 7.84/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | v1_relat_1(X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_653,plain,
% 7.84/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | ~ v1_partfun1(X0,X1)
% 7.84/1.49      | k1_relat_1(X0) = X1 ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_649,c_26,c_21,c_19]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_654,plain,
% 7.84/1.49      ( ~ v1_partfun1(X0,X1)
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | k1_relat_1(X0) = X1 ),
% 7.84/1.49      inference(renaming,[status(thm)],[c_653]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_759,plain,
% 7.84/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.84/1.49      | ~ v1_funct_1(X0)
% 7.84/1.49      | v1_xboole_0(X2)
% 7.84/1.49      | k1_relat_1(X0) = X1 ),
% 7.84/1.49      inference(resolution,[status(thm)],[c_23,c_654]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_763,plain,
% 7.84/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.84/1.49      | ~ v1_funct_1(X0)
% 7.84/1.49      | v1_xboole_0(X2)
% 7.84/1.49      | k1_relat_1(X0) = X1 ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_759,c_26,c_23,c_21,c_19]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_764,plain,
% 7.84/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | ~ v1_funct_1(X0)
% 7.84/1.49      | v1_xboole_0(X2)
% 7.84/1.49      | k1_relat_1(X0) = X1 ),
% 7.84/1.49      inference(renaming,[status(thm)],[c_763]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3296,plain,
% 7.84/1.49      ( k1_relat_1(X0) = X1
% 7.84/1.49      | v1_funct_2(X0,X1,X2) != iProver_top
% 7.84/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.84/1.49      | v1_funct_1(X0) != iProver_top
% 7.84/1.49      | v1_xboole_0(X2) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4287,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top
% 7.84/1.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3309,c_3296]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_44,negated_conjecture,
% 7.84/1.49      ( v1_funct_1(sK5) ),
% 7.84/1.49      inference(cnf_transformation,[],[f123]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_59,plain,
% 7.84/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_43,negated_conjecture,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
% 7.84/1.49      inference(cnf_transformation,[],[f124]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_60,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4813,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_4287,c_59,c_60]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_6,plain,
% 7.84/1.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.84/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3330,plain,
% 7.84/1.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4817,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 7.84/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4813,c_3330]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_33,plain,
% 7.84/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.84/1.49      | ~ l1_pre_topc(X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f110]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3317,plain,
% 7.84/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.84/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5730,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) = iProver_top
% 7.84/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4817,c_3317]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_48,negated_conjecture,
% 7.84/1.49      ( l1_pre_topc(sK3) ),
% 7.84/1.49      inference(cnf_transformation,[],[f119]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_55,plain,
% 7.84/1.49      ( l1_pre_topc(sK3) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_32,plain,
% 7.84/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.84/1.49      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.84/1.49      inference(cnf_transformation,[],[f109]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3744,plain,
% 7.84/1.49      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 7.84/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_32]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3745,plain,
% 7.84/1.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_3744]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4048,plain,
% 7.84/1.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 7.84/1.49      | ~ l1_pre_topc(sK3) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_33]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4049,plain,
% 7.84/1.49      ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_4048]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_15336,plain,
% 7.84/1.49      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) = iProver_top
% 7.84/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_5730,c_55,c_3745,c_4049]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_15337,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
% 7.84/1.49      inference(renaming,[status(thm)],[c_15336]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_22,plain,
% 7.84/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | ~ v1_xboole_0(X2)
% 7.84/1.49      | v1_xboole_0(X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3321,plain,
% 7.84/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.84/1.49      | v1_xboole_0(X2) != iProver_top
% 7.84/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_6793,plain,
% 7.84/1.49      ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3309,c_3321]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7015,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4813,c_6793]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_8596,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | sK5 = k1_xboole_0 ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_7015,c_3330]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_38,plain,
% 7.84/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.84/1.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.84/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.84/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.84/1.49      | ~ v2_pre_topc(X1)
% 7.84/1.49      | ~ v2_pre_topc(X2)
% 7.84/1.49      | ~ l1_pre_topc(X1)
% 7.84/1.49      | ~ l1_pre_topc(X2)
% 7.84/1.49      | ~ v1_funct_1(X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f136]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3312,plain,
% 7.84/1.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.84/1.49      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) = iProver_top
% 7.84/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.84/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) != iProver_top
% 7.84/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.84/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) != iProver_top
% 7.84/1.49      | v2_pre_topc(X1) != iProver_top
% 7.84/1.49      | v2_pre_topc(X2) != iProver_top
% 7.84/1.49      | l1_pre_topc(X1) != iProver_top
% 7.84/1.49      | l1_pre_topc(X2) != iProver_top
% 7.84/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_6679,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3309,c_3312]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_51,negated_conjecture,
% 7.84/1.49      ( v2_pre_topc(sK2) ),
% 7.84/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_52,plain,
% 7.84/1.49      ( v2_pre_topc(sK2) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_50,negated_conjecture,
% 7.84/1.49      ( l1_pre_topc(sK2) ),
% 7.84/1.49      inference(cnf_transformation,[],[f117]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_53,plain,
% 7.84/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_49,negated_conjecture,
% 7.84/1.49      ( v2_pre_topc(sK3) ),
% 7.84/1.49      inference(cnf_transformation,[],[f118]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_54,plain,
% 7.84/1.49      ( v2_pre_topc(sK3) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_61,plain,
% 7.84/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_34,plain,
% 7.84/1.49      ( ~ v2_pre_topc(X0)
% 7.84/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.84/1.49      | ~ l1_pre_topc(X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f111]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_76,plain,
% 7.84/1.49      ( v2_pre_topc(X0) != iProver_top
% 7.84/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 7.84/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_78,plain,
% 7.84/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.84/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_76]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_79,plain,
% 7.84/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.84/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_81,plain,
% 7.84/1.49      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 7.84/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_79]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_39,negated_conjecture,
% 7.84/1.49      ( ~ v5_pre_topc(sK4,sK2,sK3)
% 7.84/1.49      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 7.84/1.49      inference(cnf_transformation,[],[f128]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3311,plain,
% 7.84/1.49      ( v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_41,negated_conjecture,
% 7.84/1.49      ( sK4 = sK5 ),
% 7.84/1.49      inference(cnf_transformation,[],[f126]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3342,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,sK2,sK3) != iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_3311,c_41]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_40,negated_conjecture,
% 7.84/1.49      ( v5_pre_topc(sK4,sK2,sK3)
% 7.84/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
% 7.84/1.49      inference(cnf_transformation,[],[f127]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3310,plain,
% 7.84/1.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3341,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,sK2,sK3) = iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_3310,c_41]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_46,negated_conjecture,
% 7.84/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 7.84/1.49      inference(cnf_transformation,[],[f121]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3305,plain,
% 7.84/1.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3339,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_3305,c_41]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_45,negated_conjecture,
% 7.84/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 7.84/1.49      inference(cnf_transformation,[],[f122]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3306,plain,
% 7.84/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3340,plain,
% 7.84/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_3306,c_41]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3476,plain,
% 7.84/1.49      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.84/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_32]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3477,plain,
% 7.84/1.49      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top
% 7.84/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_3476]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_35,plain,
% 7.84/1.49      ( v5_pre_topc(X0,X1,X2)
% 7.84/1.49      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.84/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.84/1.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.84/1.49      | ~ v2_pre_topc(X1)
% 7.84/1.49      | ~ v2_pre_topc(X2)
% 7.84/1.49      | ~ l1_pre_topc(X1)
% 7.84/1.49      | ~ l1_pre_topc(X2)
% 7.84/1.49      | ~ v1_funct_1(X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f133]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3932,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,X0,sK3)
% 7.84/1.49      | ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
% 7.84/1.49      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 7.84/1.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
% 7.84/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 7.84/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
% 7.84/1.49      | ~ v2_pre_topc(X0)
% 7.84/1.49      | ~ v2_pre_topc(sK3)
% 7.84/1.49      | ~ l1_pre_topc(X0)
% 7.84/1.49      | ~ l1_pre_topc(sK3)
% 7.84/1.49      | ~ v1_funct_1(sK5) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_35]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3938,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,X0,sK3) = iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(X0) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(X0) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_3932]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3940,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_3938]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_36,plain,
% 7.84/1.49      ( ~ v5_pre_topc(X0,X1,X2)
% 7.84/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.84/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.84/1.49      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
% 7.84/1.49      | ~ v2_pre_topc(X1)
% 7.84/1.49      | ~ v2_pre_topc(X2)
% 7.84/1.49      | ~ l1_pre_topc(X1)
% 7.84/1.49      | ~ l1_pre_topc(X2)
% 7.84/1.49      | ~ v1_funct_1(X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f134]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5375,plain,
% 7.84/1.49      ( ~ v5_pre_topc(sK5,X0,sK3)
% 7.84/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
% 7.84/1.49      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 7.84/1.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))
% 7.84/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 7.84/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3))))
% 7.84/1.49      | ~ v2_pre_topc(X0)
% 7.84/1.49      | ~ v2_pre_topc(sK3)
% 7.84/1.49      | ~ l1_pre_topc(X0)
% 7.84/1.49      | ~ l1_pre_topc(sK3)
% 7.84/1.49      | ~ v1_funct_1(sK5) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_36]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5376,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,X0,sK3) != iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3) = iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(X0) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(X0) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_5375]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5378,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_5376]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_37,plain,
% 7.84/1.49      ( v5_pre_topc(X0,X1,X2)
% 7.84/1.49      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
% 7.84/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.84/1.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
% 7.84/1.49      | ~ v2_pre_topc(X1)
% 7.84/1.49      | ~ v2_pre_topc(X2)
% 7.84/1.49      | ~ l1_pre_topc(X1)
% 7.84/1.49      | ~ l1_pre_topc(X2)
% 7.84/1.49      | ~ v1_funct_1(X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f135]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3933,plain,
% 7.84/1.49      ( ~ v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.84/1.49      | v5_pre_topc(sK5,X0,sK3)
% 7.84/1.49      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 7.84/1.49      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 7.84/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 7.84/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 7.84/1.49      | ~ v2_pre_topc(X0)
% 7.84/1.49      | ~ v2_pre_topc(sK3)
% 7.84/1.49      | ~ l1_pre_topc(X0)
% 7.84/1.49      | ~ l1_pre_topc(sK3)
% 7.84/1.49      | ~ v1_funct_1(sK5) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_37]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5516,plain,
% 7.84/1.49      ( ~ v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.84/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
% 7.84/1.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 7.84/1.49      | ~ v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))
% 7.84/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 7.84/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))))
% 7.84/1.49      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.84/1.49      | ~ v2_pre_topc(sK3)
% 7.84/1.49      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.84/1.49      | ~ l1_pre_topc(sK3)
% 7.84/1.49      | ~ v1_funct_1(sK5) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_3933]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5517,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) = iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_5516]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7020,plain,
% 7.84/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_6679,c_52,c_53,c_54,c_55,c_59,c_60,c_61,c_78,c_81,
% 7.84/1.49                 c_3342,c_3341,c_3339,c_3340,c_3477,c_3940,c_5378,c_5517]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7021,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 7.84/1.49      inference(renaming,[status(thm)],[c_7020]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7024,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)))) != iProver_top ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_7021,c_52,c_53,c_54,c_55,c_59,c_60,c_61,c_78,c_81,
% 7.84/1.49                 c_3341,c_3339,c_3340,c_3477,c_5378,c_5517]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_10918,plain,
% 7.84/1.49      ( sK5 = k1_xboole_0
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(sK3)))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_8596,c_7024]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3308,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_10925,plain,
% 7.84/1.49      ( sK5 = k1_xboole_0
% 7.84/1.49      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_8596,c_3308]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4289,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top
% 7.84/1.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3340,c_3296]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4807,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.84/1.49      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_4289,c_59,c_3339]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_6795,plain,
% 7.84/1.49      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3340,c_3321]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_6905,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.84/1.49      | v1_xboole_0(sK5) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4807,c_6795]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_8494,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5) | sK5 = k1_xboole_0 ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_6905,c_3330]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_10924,plain,
% 7.84/1.49      ( sK5 = k1_xboole_0
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_8596,c_3309]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3314,plain,
% 7.84/1.49      ( v5_pre_topc(X0,X1,X2) != iProver_top
% 7.84/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = iProver_top
% 7.84/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.84/1.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.84/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.84/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(X1) != iProver_top
% 7.84/1.49      | v2_pre_topc(X2) != iProver_top
% 7.84/1.49      | l1_pre_topc(X1) != iProver_top
% 7.84/1.49      | l1_pre_topc(X2) != iProver_top
% 7.84/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7646,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.84/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.84/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3309,c_3314]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3491,plain,
% 7.84/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.84/1.49      | ~ v2_pre_topc(sK3)
% 7.84/1.49      | ~ l1_pre_topc(sK3) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_34]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3492,plain,
% 7.84/1.49      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_3491]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3934,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,X0,sK3) = iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(X0) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(X0) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_3933]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3936,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,sK2,sK3) = iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_3934]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3980,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.84/1.49      | ~ v5_pre_topc(sK5,X0,sK3)
% 7.84/1.49      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
% 7.84/1.49      | ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3))
% 7.84/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
% 7.84/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 7.84/1.49      | ~ v2_pre_topc(X0)
% 7.84/1.49      | ~ v2_pre_topc(sK3)
% 7.84/1.49      | ~ l1_pre_topc(X0)
% 7.84/1.49      | ~ l1_pre_topc(sK3)
% 7.84/1.49      | ~ v1_funct_1(sK5) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_38]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3981,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,X0,sK3) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(X0) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(X0) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_3980]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3983,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,sK2,sK3) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK3) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK3) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_3981]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3315,plain,
% 7.84/1.49      ( v5_pre_topc(X0,X1,X2) = iProver_top
% 7.84/1.49      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) != iProver_top
% 7.84/1.49      | v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 7.84/1.49      | v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) != iProver_top
% 7.84/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 7.84/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) != iProver_top
% 7.84/1.49      | v2_pre_topc(X1) != iProver_top
% 7.84/1.49      | v2_pre_topc(X2) != iProver_top
% 7.84/1.49      | l1_pre_topc(X1) != iProver_top
% 7.84/1.49      | l1_pre_topc(X2) != iProver_top
% 7.84/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7679,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.84/1.49      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.84/1.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.84/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3309,c_3315]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7828,plain,
% 7.84/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_7646,c_52,c_53,c_54,c_55,c_59,c_60,c_3342,c_3341,
% 7.84/1.49                 c_3339,c_3340,c_3492,c_3745,c_3936,c_3983,c_4049,c_7679]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7829,plain,
% 7.84/1.49      ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.84/1.49      inference(renaming,[status(thm)],[c_7828]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7832,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_7829,c_52,c_53,c_54,c_55,c_59,c_60,c_3341,c_3339,
% 7.84/1.49                 c_3340,c_3492,c_3745,c_3983,c_4049,c_7679]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_8816,plain,
% 7.84/1.49      ( sK5 = k1_xboole_0
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_8494,c_7832]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11265,plain,
% 7.84/1.49      ( sK5 = k1_xboole_0
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_10924,c_8816]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11268,plain,
% 7.84/1.49      ( sK5 = k1_xboole_0
% 7.84/1.49      | v1_funct_2(sK5,k1_relat_1(sK5),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_8494,c_11265]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11410,plain,
% 7.84/1.49      ( sK5 = k1_xboole_0 ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_10918,c_10925,c_11268]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_15340,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) = iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_15337,c_11410]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_15,plain,
% 7.84/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.84/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3324,plain,
% 7.84/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.84/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_15342,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_15340,c_3324]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4,plain,
% 7.84/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.84/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3332,plain,
% 7.84/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.84/1.49      | r2_hidden(X2,X0) != iProver_top
% 7.84/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_16055,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_15342,c_3332]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_19489,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0) = iProver_top
% 7.84/1.49      | r2_hidden(sK1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3333,c_16055]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4811,plain,
% 7.84/1.49      ( u1_struct_0(sK3) = k1_xboole_0
% 7.84/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4807,c_3330]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11452,plain,
% 7.84/1.49      ( u1_struct_0(sK3) = k1_xboole_0
% 7.84/1.49      | u1_struct_0(sK2) = k1_relat_1(k1_xboole_0) ),
% 7.84/1.49      inference(demodulation,[status(thm)],[c_11410,c_4811]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1,plain,
% 7.84/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.84/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3335,plain,
% 7.84/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.84/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5217,plain,
% 7.84/1.49      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3333,c_3335]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_14,plain,
% 7.84/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.84/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3325,plain,
% 7.84/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.84/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7836,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3325,c_7832]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_8967,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_5217,c_7836]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5,plain,
% 7.84/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_151,plain,
% 7.84/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_2344,plain,
% 7.84/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.84/1.49      theory(equality) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_6672,plain,
% 7.84/1.49      ( v1_xboole_0(X0)
% 7.84/1.49      | ~ v1_xboole_0(k1_xboole_0)
% 7.84/1.49      | X0 != k1_xboole_0 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_2344]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_13181,plain,
% 7.84/1.49      ( v1_xboole_0(sK5)
% 7.84/1.49      | ~ v1_xboole_0(k1_xboole_0)
% 7.84/1.49      | sK5 != k1_xboole_0 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_6672]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_13185,plain,
% 7.84/1.49      ( sK5 != k1_xboole_0
% 7.84/1.49      | v1_xboole_0(sK5) = iProver_top
% 7.84/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_13181]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_15121,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_8967,c_151,c_10925,c_11268,c_13185]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_15125,plain,
% 7.84/1.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_15121,c_11410]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_16432,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | v1_funct_2(k1_xboole_0,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_11452,c_15125]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3331,plain,
% 7.84/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_12,plain,
% 7.84/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.84/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3326,plain,
% 7.84/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11,plain,
% 7.84/1.49      ( k2_subset_1(X0) = X0 ),
% 7.84/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3338,plain,
% 7.84/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_3326,c_11]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_6794,plain,
% 7.84/1.49      ( v1_xboole_0(X0) != iProver_top
% 7.84/1.49      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3338,c_3321]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_9594,plain,
% 7.84/1.49      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 7.84/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_6794,c_3330]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_9599,plain,
% 7.84/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3331,c_9594]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3322,plain,
% 7.84/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.84/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5222,plain,
% 7.84/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3338,c_3322]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_9725,plain,
% 7.84/1.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_9599,c_5222]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_47,negated_conjecture,
% 7.84/1.49      ( v1_funct_1(sK4) ),
% 7.84/1.49      inference(cnf_transformation,[],[f120]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3304,plain,
% 7.84/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3337,plain,
% 7.84/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_3304,c_41]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11465,plain,
% 7.84/1.49      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 7.84/1.49      inference(demodulation,[status(thm)],[c_11410,c_3337]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_8,plain,
% 7.84/1.49      ( r1_tarski(X0,X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f129]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_13411,plain,
% 7.84/1.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_13412,plain,
% 7.84/1.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_13411]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_30,plain,
% 7.84/1.49      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.84/1.49      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.84/1.49      | ~ v1_funct_1(X0)
% 7.84/1.49      | ~ v1_relat_1(X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f107]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3319,plain,
% 7.84/1.49      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 7.84/1.49      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.84/1.49      | v1_funct_1(X0) != iProver_top
% 7.84/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4989,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.84/1.49      | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK3)))) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4811,c_4813]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4997,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4811,c_3340]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4998,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),k1_xboole_0) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4811,c_3339]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7837,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4817,c_7832]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_8008,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(sK2),k1_xboole_0) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),k1_xboole_0))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4817,c_7837]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11720,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.84/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5) ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_4989,c_4997,c_4998,c_8008]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11721,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5) ),
% 7.84/1.49      inference(renaming,[status(thm)],[c_11720]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11722,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | u1_struct_0(sK2) = k1_relat_1(k1_xboole_0) ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_11721,c_11410]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5667,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4817,c_3309]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7029,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_xboole_0))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4811,c_7024]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_8005,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(sK5)
% 7.84/1.49      | u1_struct_0(sK2) = k1_relat_1(sK5)
% 7.84/1.49      | v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_5667,c_7029]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7028,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3))) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3325,c_7024]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_8966,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top
% 7.84/1.49      | v1_xboole_0(sK5) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_5217,c_7028]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_13476,plain,
% 7.84/1.49      ( v1_funct_2(sK5,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_8005,c_151,c_8966,c_10925,c_11268,c_13185]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_13480,plain,
% 7.84/1.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_13476,c_11410]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_13482,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_11722,c_13480]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_22426,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_11452,c_13482]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_22567,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 7.84/1.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.84/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3319,c_22426]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_10,plain,
% 7.84/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3327,plain,
% 7.84/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_20,plain,
% 7.84/1.49      ( v5_relat_1(X0,X1)
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.84/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_17,plain,
% 7.84/1.49      ( ~ v5_relat_1(X0,X1)
% 7.84/1.49      | r1_tarski(k2_relat_1(X0),X1)
% 7.84/1.49      | ~ v1_relat_1(X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_628,plain,
% 7.84/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | r1_tarski(k2_relat_1(X0),X2)
% 7.84/1.49      | ~ v1_relat_1(X0) ),
% 7.84/1.49      inference(resolution,[status(thm)],[c_20,c_17]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_632,plain,
% 7.84/1.49      ( r1_tarski(k2_relat_1(X0),X2)
% 7.84/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_628,c_19]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_633,plain,
% 7.84/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.84/1.49      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.84/1.49      inference(renaming,[status(thm)],[c_632]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3298,plain,
% 7.84/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.84/1.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5674,plain,
% 7.84/1.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.84/1.49      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3325,c_3298]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_12714,plain,
% 7.84/1.49      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3327,c_5674]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_7,plain,
% 7.84/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.84/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3329,plain,
% 7.84/1.49      ( X0 = X1
% 7.84/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.84/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.84/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_5925,plain,
% 7.84/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3327,c_3329]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_12872,plain,
% 7.84/1.49      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_12714,c_5925]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_22568,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.84/1.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.84/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_22567,c_12872]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_22571,plain,
% 7.84/1.49      ( u1_struct_0(sK2) = k1_relat_1(k1_xboole_0) ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_16432,c_9725,c_11465,c_13412,c_22568]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_23676,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0) = iProver_top
% 7.84/1.49      | r2_hidden(sK1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_19489,c_22571]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11445,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k1_xboole_0
% 7.84/1.49      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0) ),
% 7.84/1.49      inference(demodulation,[status(thm)],[c_11410,c_4817]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_17401,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | v1_funct_2(k1_xboole_0,u1_struct_0(sK2),k1_xboole_0) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_11445,c_15125]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_23595,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_17401,c_22571]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_23597,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 7.84/1.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.84/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3319,c_23595]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_23598,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0)
% 7.84/1.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.84/1.49      | v1_funct_1(k1_xboole_0) != iProver_top
% 7.84/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.84/1.49      inference(light_normalisation,[status(thm)],[c_23597,c_12872]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_23680,plain,
% 7.84/1.49      ( u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))) = k1_relat_1(k1_xboole_0) ),
% 7.84/1.49      inference(global_propositional_subsumption,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_23676,c_9725,c_11465,c_13412,c_23598]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_22603,plain,
% 7.84/1.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK2))),u1_struct_0(sK3)) != iProver_top ),
% 7.84/1.49      inference(demodulation,[status(thm)],[c_22571,c_13480]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_23682,plain,
% 7.84/1.49      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) != iProver_top ),
% 7.84/1.49      inference(demodulation,[status(thm)],[c_23680,c_22603]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_11464,plain,
% 7.84/1.49      ( v1_funct_2(k1_xboole_0,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 7.84/1.49      inference(demodulation,[status(thm)],[c_11410,c_3339]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_22612,plain,
% 7.84/1.49      ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK3)) = iProver_top ),
% 7.84/1.49      inference(demodulation,[status(thm)],[c_22571,c_11464]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(contradiction,plain,
% 7.84/1.49      ( $false ),
% 7.84/1.49      inference(minisat,[status(thm)],[c_23682,c_22612]) ).
% 7.84/1.49  
% 7.84/1.49  
% 7.84/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.84/1.49  
% 7.84/1.49  ------                               Statistics
% 7.84/1.49  
% 7.84/1.49  ------ General
% 7.84/1.49  
% 7.84/1.49  abstr_ref_over_cycles:                  0
% 7.84/1.49  abstr_ref_under_cycles:                 0
% 7.84/1.49  gc_basic_clause_elim:                   0
% 7.84/1.49  forced_gc_time:                         0
% 7.84/1.49  parsing_time:                           0.01
% 7.84/1.49  unif_index_cands_time:                  0.
% 7.84/1.49  unif_index_add_time:                    0.
% 7.84/1.49  orderings_time:                         0.
% 7.84/1.49  out_proof_time:                         0.022
% 7.84/1.49  total_time:                             0.787
% 7.84/1.49  num_of_symbols:                         59
% 7.84/1.49  num_of_terms:                           17408
% 7.84/1.49  
% 7.84/1.49  ------ Preprocessing
% 7.84/1.49  
% 7.84/1.49  num_of_splits:                          0
% 7.84/1.49  num_of_split_atoms:                     0
% 7.84/1.49  num_of_reused_defs:                     0
% 7.84/1.49  num_eq_ax_congr_red:                    31
% 7.84/1.49  num_of_sem_filtered_clauses:            1
% 7.84/1.49  num_of_subtypes:                        0
% 7.84/1.49  monotx_restored_types:                  0
% 7.84/1.49  sat_num_of_epr_types:                   0
% 7.84/1.49  sat_num_of_non_cyclic_types:            0
% 7.84/1.49  sat_guarded_non_collapsed_types:        0
% 7.84/1.49  num_pure_diseq_elim:                    0
% 7.84/1.49  simp_replaced_by:                       0
% 7.84/1.49  res_preprocessed:                       214
% 7.84/1.49  prep_upred:                             0
% 7.84/1.49  prep_unflattend:                        42
% 7.84/1.49  smt_new_axioms:                         0
% 7.84/1.49  pred_elim_cands:                        10
% 7.84/1.49  pred_elim:                              3
% 7.84/1.49  pred_elim_cl:                           5
% 7.84/1.49  pred_elim_cycles:                       7
% 7.84/1.49  merged_defs:                            16
% 7.84/1.49  merged_defs_ncl:                        0
% 7.84/1.49  bin_hyper_res:                          17
% 7.84/1.49  prep_cycles:                            4
% 7.84/1.49  pred_elim_time:                         0.032
% 7.84/1.49  splitting_time:                         0.
% 7.84/1.49  sem_filter_time:                        0.
% 7.84/1.49  monotx_time:                            0.
% 7.84/1.49  subtype_inf_time:                       0.
% 7.84/1.49  
% 7.84/1.49  ------ Problem properties
% 7.84/1.49  
% 7.84/1.49  clauses:                                44
% 7.84/1.49  conjectures:                            13
% 7.84/1.49  epr:                                    16
% 7.84/1.49  horn:                                   39
% 7.84/1.49  ground:                                 14
% 7.84/1.49  unary:                                  16
% 7.84/1.49  binary:                                 14
% 7.84/1.49  lits:                                   126
% 7.84/1.49  lits_eq:                                8
% 7.84/1.49  fd_pure:                                0
% 7.84/1.49  fd_pseudo:                              0
% 7.84/1.49  fd_cond:                                1
% 7.84/1.49  fd_pseudo_cond:                         3
% 7.84/1.49  ac_symbols:                             0
% 7.84/1.49  
% 7.84/1.49  ------ Propositional Solver
% 7.84/1.49  
% 7.84/1.49  prop_solver_calls:                      32
% 7.84/1.49  prop_fast_solver_calls:                 3488
% 7.84/1.49  smt_solver_calls:                       0
% 7.84/1.49  smt_fast_solver_calls:                  0
% 7.84/1.49  prop_num_of_clauses:                    9560
% 7.84/1.49  prop_preprocess_simplified:             19743
% 7.84/1.49  prop_fo_subsumed:                       222
% 7.84/1.49  prop_solver_time:                       0.
% 7.84/1.49  smt_solver_time:                        0.
% 7.84/1.49  smt_fast_solver_time:                   0.
% 7.84/1.49  prop_fast_solver_time:                  0.
% 7.84/1.49  prop_unsat_core_time:                   0.
% 7.84/1.49  
% 7.84/1.49  ------ QBF
% 7.84/1.49  
% 7.84/1.49  qbf_q_res:                              0
% 7.84/1.49  qbf_num_tautologies:                    0
% 7.84/1.49  qbf_prep_cycles:                        0
% 7.84/1.49  
% 7.84/1.49  ------ BMC1
% 7.84/1.49  
% 7.84/1.49  bmc1_current_bound:                     -1
% 7.84/1.49  bmc1_last_solved_bound:                 -1
% 7.84/1.49  bmc1_unsat_core_size:                   -1
% 7.84/1.49  bmc1_unsat_core_parents_size:           -1
% 7.84/1.49  bmc1_merge_next_fun:                    0
% 7.84/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.84/1.49  
% 7.84/1.49  ------ Instantiation
% 7.84/1.49  
% 7.84/1.49  inst_num_of_clauses:                    2417
% 7.84/1.49  inst_num_in_passive:                    996
% 7.84/1.49  inst_num_in_active:                     941
% 7.84/1.49  inst_num_in_unprocessed:                480
% 7.84/1.49  inst_num_of_loops:                      1460
% 7.84/1.49  inst_num_of_learning_restarts:          0
% 7.84/1.49  inst_num_moves_active_passive:          516
% 7.84/1.49  inst_lit_activity:                      0
% 7.84/1.49  inst_lit_activity_moves:                0
% 7.84/1.49  inst_num_tautologies:                   0
% 7.84/1.49  inst_num_prop_implied:                  0
% 7.84/1.49  inst_num_existing_simplified:           0
% 7.84/1.49  inst_num_eq_res_simplified:             0
% 7.84/1.49  inst_num_child_elim:                    0
% 7.84/1.49  inst_num_of_dismatching_blockings:      747
% 7.84/1.49  inst_num_of_non_proper_insts:           3147
% 7.84/1.49  inst_num_of_duplicates:                 0
% 7.84/1.49  inst_inst_num_from_inst_to_res:         0
% 7.84/1.49  inst_dismatching_checking_time:         0.
% 7.84/1.49  
% 7.84/1.49  ------ Resolution
% 7.84/1.49  
% 7.84/1.49  res_num_of_clauses:                     0
% 7.84/1.49  res_num_in_passive:                     0
% 7.84/1.49  res_num_in_active:                      0
% 7.84/1.49  res_num_of_loops:                       218
% 7.84/1.49  res_forward_subset_subsumed:            296
% 7.84/1.49  res_backward_subset_subsumed:           0
% 7.84/1.49  res_forward_subsumed:                   0
% 7.84/1.49  res_backward_subsumed:                  0
% 7.84/1.49  res_forward_subsumption_resolution:     1
% 7.84/1.49  res_backward_subsumption_resolution:    0
% 7.84/1.49  res_clause_to_clause_subsumption:       2201
% 7.84/1.49  res_orphan_elimination:                 0
% 7.84/1.49  res_tautology_del:                      240
% 7.84/1.49  res_num_eq_res_simplified:              0
% 7.84/1.49  res_num_sel_changes:                    0
% 7.84/1.49  res_moves_from_active_to_pass:          0
% 7.84/1.49  
% 7.84/1.49  ------ Superposition
% 7.84/1.49  
% 7.84/1.49  sup_time_total:                         0.
% 7.84/1.49  sup_time_generating:                    0.
% 7.84/1.49  sup_time_sim_full:                      0.
% 7.84/1.49  sup_time_sim_immed:                     0.
% 7.84/1.49  
% 7.84/1.49  sup_num_of_clauses:                     349
% 7.84/1.49  sup_num_in_active:                      117
% 7.84/1.49  sup_num_in_passive:                     232
% 7.84/1.49  sup_num_of_loops:                       291
% 7.84/1.49  sup_fw_superposition:                   593
% 7.84/1.49  sup_bw_superposition:                   639
% 7.84/1.49  sup_immediate_simplified:               326
% 7.84/1.49  sup_given_eliminated:                   3
% 7.84/1.49  comparisons_done:                       0
% 7.84/1.49  comparisons_avoided:                    31
% 7.84/1.49  
% 7.84/1.49  ------ Simplifications
% 7.84/1.49  
% 7.84/1.49  
% 7.84/1.49  sim_fw_subset_subsumed:                 208
% 7.84/1.49  sim_bw_subset_subsumed:                 280
% 7.84/1.49  sim_fw_subsumed:                        80
% 7.84/1.49  sim_bw_subsumed:                        6
% 7.84/1.49  sim_fw_subsumption_res:                 0
% 7.84/1.49  sim_bw_subsumption_res:                 0
% 7.84/1.49  sim_tautology_del:                      15
% 7.84/1.49  sim_eq_tautology_del:                   44
% 7.84/1.49  sim_eq_res_simp:                        0
% 7.84/1.49  sim_fw_demodulated:                     31
% 7.84/1.49  sim_bw_demodulated:                     104
% 7.84/1.49  sim_light_normalised:                   157
% 7.84/1.49  sim_joinable_taut:                      0
% 7.84/1.49  sim_joinable_simp:                      0
% 7.84/1.49  sim_ac_normalised:                      0
% 7.84/1.49  sim_smt_subsumption:                    0
% 7.84/1.49  
%------------------------------------------------------------------------------
