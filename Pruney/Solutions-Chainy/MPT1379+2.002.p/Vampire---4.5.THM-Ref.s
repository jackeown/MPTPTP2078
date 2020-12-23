%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:57 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  127 (1798 expanded)
%              Number of leaves         :   14 ( 645 expanded)
%              Depth                    :   29
%              Number of atoms          :  587 (18817 expanded)
%              Number of equality atoms :   27 ( 168 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1568,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1559,f635])).

fof(f635,plain,(
    r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f634,f93])).

fof(f93,plain,(
    ! [X1] :
      ( ~ m1_connsp_2(X1,sK0,sK1)
      | r2_hidden(sK1,k1_tops_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f92,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f88,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
      | ~ m1_connsp_2(sK3,sK0,sK1)
      | ~ m1_connsp_2(sK2,sK0,sK1) )
    & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
      | ( m1_connsp_2(sK3,sK0,sK1)
        & m1_connsp_2(sK2,sK0,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ~ m1_connsp_2(X3,X0,X1)
                      | ~ m1_connsp_2(X2,X0,X1) )
                    & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                    | ~ m1_connsp_2(X3,sK0,X1)
                    | ~ m1_connsp_2(X2,sK0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                    | ( m1_connsp_2(X3,sK0,X1)
                      & m1_connsp_2(X2,sK0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                  | ~ m1_connsp_2(X3,sK0,X1)
                  | ~ m1_connsp_2(X2,sK0,X1) )
                & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                  | ( m1_connsp_2(X3,sK0,X1)
                    & m1_connsp_2(X2,sK0,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
                | ~ m1_connsp_2(X3,sK0,sK1)
                | ~ m1_connsp_2(X2,sK0,sK1) )
              & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
                | ( m1_connsp_2(X3,sK0,sK1)
                  & m1_connsp_2(X2,sK0,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
              | ~ m1_connsp_2(X3,sK0,sK1)
              | ~ m1_connsp_2(X2,sK0,sK1) )
            & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
              | ( m1_connsp_2(X3,sK0,sK1)
                & m1_connsp_2(X2,sK0,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
            | ~ m1_connsp_2(X3,sK0,sK1)
            | ~ m1_connsp_2(sK2,sK0,sK1) )
          & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
            | ( m1_connsp_2(X3,sK0,sK1)
              & m1_connsp_2(sK2,sK0,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
          | ~ m1_connsp_2(X3,sK0,sK1)
          | ~ m1_connsp_2(sK2,sK0,sK1) )
        & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
          | ( m1_connsp_2(X3,sK0,sK1)
            & m1_connsp_2(sK2,sK0,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
        | ~ m1_connsp_2(sK3,sK0,sK1)
        | ~ m1_connsp_2(sK2,sK0,sK1) )
      & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
        | ( m1_connsp_2(sK3,sK0,sK1)
          & m1_connsp_2(sK2,sK0,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_connsp_2(X2,X0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_connsp_2(X2,X0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                    <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f40,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f40,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    ! [X1] :
      ( r2_hidden(sK1,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f91,f37])).

fof(f91,plain,(
    ! [X1] :
      ( r2_hidden(sK1,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f90,f38])).

fof(f90,plain,(
    ! [X1] :
      ( r2_hidden(sK1,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f39])).

fof(f85,plain,(
    ! [X1] :
      ( r2_hidden(sK1,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f634,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(forward_demodulation,[],[f631,f308])).

fof(f308,plain,(
    k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) ),
    inference(resolution,[],[f190,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f190,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,k3_xboole_0(X1,sK3)) = k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) ) ),
    inference(backward_demodulation,[],[f130,f179])).

fof(f179,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,k1_tops_1(sK0,sK3)) = k3_xboole_0(X4,k1_tops_1(sK0,sK3)) ),
    inference(resolution,[],[f122,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f122,plain,(
    m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f115,f39])).

fof(f115,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f130,plain,(
    ! [X1] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(X1,sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f126,f120])).

fof(f120,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK3) = k3_xboole_0(X4,sK3) ),
    inference(resolution,[],[f42,f54])).

fof(f126,plain,(
    ! [X1] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f125,f38])).

fof(f125,plain,(
    ! [X1] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f39])).

fof(f117,plain,(
    ! [X1] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f42,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tops_1)).

fof(f631,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f626])).

fof(f626,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(resolution,[],[f208,f147])).

fof(f147,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(subsumption_resolution,[],[f146,f37])).

fof(f146,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f145,f38])).

fof(f145,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f144,f39])).

fof(f144,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f143,f40])).

fof(f143,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f142,f42])).

fof(f142,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f132,f46])).

fof(f132,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(backward_demodulation,[],[f44,f120])).

fof(f44,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f208,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),X0))
      | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ) ),
    inference(resolution,[],[f140,f61])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f140,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(subsumption_resolution,[],[f139,f37])).

fof(f139,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f138,f38])).

fof(f138,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f137,f39])).

fof(f137,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f136,f40])).

fof(f136,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f135,f41])).

fof(f135,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f131,f46])).

fof(f131,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(backward_demodulation,[],[f43,f120])).

fof(f43,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f1559,plain,(
    ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) ),
    inference(resolution,[],[f525,f1540])).

fof(f1540,plain,(
    ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f1539,f673])).

fof(f673,plain,(
    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(subsumption_resolution,[],[f672,f37])).

fof(f672,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f671,f38])).

fof(f671,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f670,f39])).

fof(f670,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f669,f40])).

fof(f669,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f662,f192])).

fof(f192,plain,(
    ! [X2] : m1_subset_1(k3_xboole_0(sK2,X2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f113,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f113,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f103,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f103,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f41,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f662,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f635,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1539,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f1530,f635])).

fof(f1530,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f524,f268])).

fof(f268,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f266,f41])).

fof(f266,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f156,f96])).

fof(f96,plain,(
    ! [X2] :
      ( m1_connsp_2(X2,sK0,sK1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f95,f37])).

fof(f95,plain,(
    ! [X2] :
      ( m1_connsp_2(X2,sK0,sK1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f38])).

fof(f94,plain,(
    ! [X2] :
      ( m1_connsp_2(X2,sK0,sK1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f39])).

fof(f86,plain,(
    ! [X2] :
      ( m1_connsp_2(X2,sK0,sK1)
      | ~ r2_hidden(sK1,k1_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f40,f47])).

fof(f156,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    inference(subsumption_resolution,[],[f155,f37])).

fof(f155,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f154,f38])).

fof(f154,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f153,f39])).

fof(f153,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f40])).

fof(f152,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f42])).

fof(f151,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f133,f47])).

fof(f133,plain,
    ( ~ m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f45,f120])).

fof(f45,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f524,plain,(
    ! [X5] :
      ( r2_hidden(X5,k1_tops_1(sK0,sK3))
      | ~ r2_hidden(X5,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) ) ),
    inference(superposition,[],[f62,f308])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f525,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_tops_1(sK0,sK2))
      | ~ r2_hidden(X6,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) ) ),
    inference(superposition,[],[f63,f308])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:58:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.44  % (13353)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.45  % (13363)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.45  % (13357)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.45  % (13355)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (13352)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  % (13350)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (13350)Refutation not found, incomplete strategy% (13350)------------------------------
% 0.20/0.46  % (13350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (13351)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.46  % (13354)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (13360)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % (13369)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (13367)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (13369)Refutation not found, incomplete strategy% (13369)------------------------------
% 0.20/0.47  % (13369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (13369)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (13369)Memory used [KB]: 10618
% 0.20/0.47  % (13369)Time elapsed: 0.080 s
% 0.20/0.47  % (13369)------------------------------
% 0.20/0.47  % (13369)------------------------------
% 0.20/0.47  % (13356)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (13359)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (13362)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (13361)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (13358)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (13350)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (13350)Memory used [KB]: 10618
% 0.20/0.47  % (13350)Time elapsed: 0.056 s
% 0.20/0.47  % (13350)------------------------------
% 0.20/0.47  % (13350)------------------------------
% 0.20/0.47  % (13368)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (13365)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (13366)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (13364)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (13349)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.49/0.54  % (13353)Refutation found. Thanks to Tanya!
% 1.49/0.54  % SZS status Theorem for theBenchmark
% 1.62/0.55  % SZS output start Proof for theBenchmark
% 1.62/0.55  fof(f1568,plain,(
% 1.62/0.55    $false),
% 1.62/0.55    inference(subsumption_resolution,[],[f1559,f635])).
% 1.62/0.55  fof(f635,plain,(
% 1.62/0.55    r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))),
% 1.62/0.55    inference(subsumption_resolution,[],[f634,f93])).
% 1.62/0.55  fof(f93,plain,(
% 1.62/0.55    ( ! [X1] : (~m1_connsp_2(X1,sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,X1))) )),
% 1.62/0.55    inference(subsumption_resolution,[],[f92,f89])).
% 1.62/0.55  fof(f89,plain,(
% 1.62/0.55    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.62/0.55    inference(subsumption_resolution,[],[f88,f37])).
% 1.62/0.55  fof(f37,plain,(
% 1.62/0.55    ~v2_struct_0(sK0)),
% 1.62/0.55    inference(cnf_transformation,[],[f29])).
% 1.62/0.55  fof(f29,plain,(
% 1.62/0.55    ((((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK3,sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | (m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.62/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f28,f27,f26,f25])).
% 1.62/0.55  fof(f25,plain,(
% 1.62/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | ~m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) | ~m1_connsp_2(X3,sK0,X1) | ~m1_connsp_2(X2,sK0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) | (m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.62/0.55    introduced(choice_axiom,[])).
% 1.62/0.55  fof(f26,plain,(
% 1.62/0.55    ? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) | ~m1_connsp_2(X3,sK0,X1) | ~m1_connsp_2(X2,sK0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) | (m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_connsp_2(X2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) | (m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.62/0.55    introduced(choice_axiom,[])).
% 1.62/0.55  fof(f27,plain,(
% 1.62/0.55    ? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_connsp_2(X2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) | (m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) | (m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.62/0.55    introduced(choice_axiom,[])).
% 1.62/0.55  fof(f28,plain,(
% 1.62/0.55    ? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) | (m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK3,sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | (m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.62/0.55    introduced(choice_axiom,[])).
% 1.62/0.55  fof(f24,plain,(
% 1.62/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | ~m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.62/0.55    inference(flattening,[],[f23])).
% 1.62/0.55  fof(f23,plain,(
% 1.62/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | (~m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(X2,X0,X1))) & (m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.62/0.55    inference(nnf_transformation,[],[f12])).
% 1.62/0.56  fof(f12,plain,(
% 1.62/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.62/0.56    inference(flattening,[],[f11])).
% 1.62/0.56  fof(f11,plain,(
% 1.62/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.62/0.56    inference(ennf_transformation,[],[f10])).
% 1.62/0.56  fof(f10,negated_conjecture,(
% 1.62/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 1.62/0.56    inference(negated_conjecture,[],[f9])).
% 1.62/0.56  fof(f9,conjecture,(
% 1.62/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).
% 1.62/0.56  fof(f88,plain,(
% 1.62/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,sK1) | v2_struct_0(sK0)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f87,f38])).
% 1.62/0.56  fof(f38,plain,(
% 1.62/0.56    v2_pre_topc(sK0)),
% 1.62/0.56    inference(cnf_transformation,[],[f29])).
% 1.62/0.56  fof(f87,plain,(
% 1.62/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f84,f39])).
% 1.62/0.56  fof(f39,plain,(
% 1.62/0.56    l1_pre_topc(sK0)),
% 1.62/0.56    inference(cnf_transformation,[],[f29])).
% 1.62/0.56  fof(f84,plain,(
% 1.62/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.62/0.56    inference(resolution,[],[f40,f49])).
% 1.62/0.56  fof(f49,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.62/0.56    inference(cnf_transformation,[],[f18])).
% 1.62/0.56  fof(f18,plain,(
% 1.62/0.56    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.62/0.56    inference(flattening,[],[f17])).
% 1.62/0.56  fof(f17,plain,(
% 1.62/0.56    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.62/0.56    inference(ennf_transformation,[],[f8])).
% 1.62/0.56  fof(f8,axiom,(
% 1.62/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.62/0.56  fof(f40,plain,(
% 1.62/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.62/0.56    inference(cnf_transformation,[],[f29])).
% 1.62/0.56  fof(f92,plain,(
% 1.62/0.56    ( ! [X1] : (r2_hidden(sK1,k1_tops_1(sK0,X1)) | ~m1_connsp_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f91,f37])).
% 1.62/0.56  fof(f91,plain,(
% 1.62/0.56    ( ! [X1] : (r2_hidden(sK1,k1_tops_1(sK0,X1)) | ~m1_connsp_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f90,f38])).
% 1.62/0.56  fof(f90,plain,(
% 1.62/0.56    ( ! [X1] : (r2_hidden(sK1,k1_tops_1(sK0,X1)) | ~m1_connsp_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f85,f39])).
% 1.62/0.56  fof(f85,plain,(
% 1.62/0.56    ( ! [X1] : (r2_hidden(sK1,k1_tops_1(sK0,X1)) | ~m1_connsp_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.62/0.56    inference(resolution,[],[f40,f46])).
% 1.62/0.56  fof(f46,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.62/0.56    inference(cnf_transformation,[],[f30])).
% 1.62/0.56  fof(f30,plain,(
% 1.62/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.62/0.56    inference(nnf_transformation,[],[f14])).
% 1.62/0.56  fof(f14,plain,(
% 1.62/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.62/0.56    inference(flattening,[],[f13])).
% 1.62/0.56  fof(f13,plain,(
% 1.62/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.62/0.56    inference(ennf_transformation,[],[f7])).
% 1.62/0.56  fof(f7,axiom,(
% 1.62/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.62/0.56  fof(f634,plain,(
% 1.62/0.56    r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)),
% 1.62/0.56    inference(forward_demodulation,[],[f631,f308])).
% 1.62/0.56  fof(f308,plain,(
% 1.62/0.56    k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))),
% 1.62/0.56    inference(resolution,[],[f190,f41])).
% 1.62/0.56  fof(f41,plain,(
% 1.62/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.56    inference(cnf_transformation,[],[f29])).
% 1.62/0.56  fof(f190,plain,(
% 1.62/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,k3_xboole_0(X1,sK3)) = k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3))) )),
% 1.62/0.56    inference(backward_demodulation,[],[f130,f179])).
% 1.62/0.56  fof(f179,plain,(
% 1.62/0.56    ( ! [X4] : (k9_subset_1(u1_struct_0(sK0),X4,k1_tops_1(sK0,sK3)) = k3_xboole_0(X4,k1_tops_1(sK0,sK3))) )),
% 1.62/0.56    inference(resolution,[],[f122,f54])).
% 1.62/0.56  fof(f54,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.62/0.56    inference(cnf_transformation,[],[f22])).
% 1.62/0.56  fof(f22,plain,(
% 1.62/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.62/0.56    inference(ennf_transformation,[],[f3])).
% 1.62/0.56  fof(f3,axiom,(
% 1.62/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.62/0.56  fof(f122,plain,(
% 1.62/0.56    m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.56    inference(subsumption_resolution,[],[f115,f39])).
% 1.62/0.56  fof(f115,plain,(
% 1.62/0.56    m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.62/0.56    inference(resolution,[],[f42,f50])).
% 1.62/0.56  fof(f50,plain,(
% 1.62/0.56    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.62/0.56    inference(cnf_transformation,[],[f20])).
% 1.62/0.56  fof(f20,plain,(
% 1.62/0.56    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.62/0.56    inference(flattening,[],[f19])).
% 1.62/0.56  fof(f19,plain,(
% 1.62/0.56    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.62/0.56    inference(ennf_transformation,[],[f5])).
% 1.62/0.56  fof(f5,axiom,(
% 1.62/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.62/0.56  fof(f42,plain,(
% 1.62/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.56    inference(cnf_transformation,[],[f29])).
% 1.62/0.56  fof(f130,plain,(
% 1.62/0.56    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(X1,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.62/0.56    inference(backward_demodulation,[],[f126,f120])).
% 1.62/0.56  fof(f120,plain,(
% 1.62/0.56    ( ! [X4] : (k9_subset_1(u1_struct_0(sK0),X4,sK3) = k3_xboole_0(X4,sK3)) )),
% 1.62/0.56    inference(resolution,[],[f42,f54])).
% 1.62/0.56  fof(f126,plain,(
% 1.62/0.56    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f125,f38])).
% 1.62/0.56  fof(f125,plain,(
% 1.62/0.56    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f117,f39])).
% 1.62/0.56  fof(f117,plain,(
% 1.62/0.56    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 1.62/0.56    inference(resolution,[],[f42,f48])).
% 1.62/0.56  fof(f48,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.62/0.56    inference(cnf_transformation,[],[f16])).
% 1.62/0.56  fof(f16,plain,(
% 1.62/0.56    ! [X0] : (! [X1] : (! [X2] : (k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.62/0.56    inference(flattening,[],[f15])).
% 1.62/0.56  fof(f15,plain,(
% 1.62/0.56    ! [X0] : (! [X1] : (! [X2] : (k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.62/0.56    inference(ennf_transformation,[],[f6])).
% 1.62/0.56  fof(f6,axiom,(
% 1.62/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tops_1)).
% 1.62/0.56  fof(f631,plain,(
% 1.62/0.56    r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))) | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)),
% 1.62/0.56    inference(duplicate_literal_removal,[],[f626])).
% 1.62/0.56  fof(f626,plain,(
% 1.62/0.56    r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))) | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)),
% 1.62/0.56    inference(resolution,[],[f208,f147])).
% 1.62/0.56  fof(f147,plain,(
% 1.62/0.56    r2_hidden(sK1,k1_tops_1(sK0,sK3)) | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)),
% 1.62/0.56    inference(subsumption_resolution,[],[f146,f37])).
% 1.62/0.56  fof(f146,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,sK3)) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f145,f38])).
% 1.62/0.56  fof(f145,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f144,f39])).
% 1.62/0.56  fof(f144,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f143,f40])).
% 1.62/0.56  fof(f143,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f142,f42])).
% 1.62/0.56  fof(f142,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(resolution,[],[f132,f46])).
% 1.62/0.56  fof(f132,plain,(
% 1.62/0.56    m1_connsp_2(sK3,sK0,sK1) | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)),
% 1.62/0.56    inference(backward_demodulation,[],[f44,f120])).
% 1.62/0.56  fof(f44,plain,(
% 1.62/0.56    m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | m1_connsp_2(sK3,sK0,sK1)),
% 1.62/0.56    inference(cnf_transformation,[],[f29])).
% 1.62/0.56  fof(f208,plain,(
% 1.62/0.56    ( ! [X0] : (~r2_hidden(sK1,X0) | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),X0)) | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)) )),
% 1.62/0.56    inference(resolution,[],[f140,f61])).
% 1.62/0.56  fof(f61,plain,(
% 1.62/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.62/0.56    inference(equality_resolution,[],[f57])).
% 1.62/0.56  fof(f57,plain,(
% 1.62/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.62/0.56    inference(cnf_transformation,[],[f36])).
% 1.62/0.56  fof(f36,plain,(
% 1.62/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.62/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 1.62/0.56  fof(f35,plain,(
% 1.62/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.62/0.56    introduced(choice_axiom,[])).
% 1.62/0.56  fof(f34,plain,(
% 1.62/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.62/0.56    inference(rectify,[],[f33])).
% 1.62/0.56  fof(f33,plain,(
% 1.62/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.62/0.56    inference(flattening,[],[f32])).
% 1.62/0.56  fof(f32,plain,(
% 1.62/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.62/0.56    inference(nnf_transformation,[],[f1])).
% 1.62/0.56  fof(f1,axiom,(
% 1.62/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.62/0.56  fof(f140,plain,(
% 1.62/0.56    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)),
% 1.62/0.56    inference(subsumption_resolution,[],[f139,f37])).
% 1.62/0.56  fof(f139,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f138,f38])).
% 1.62/0.56  fof(f138,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f137,f39])).
% 1.62/0.56  fof(f137,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f136,f40])).
% 1.62/0.56  fof(f136,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f135,f41])).
% 1.62/0.56  fof(f135,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(resolution,[],[f131,f46])).
% 1.62/0.56  fof(f131,plain,(
% 1.62/0.56    m1_connsp_2(sK2,sK0,sK1) | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)),
% 1.62/0.56    inference(backward_demodulation,[],[f43,f120])).
% 1.62/0.56  fof(f43,plain,(
% 1.62/0.56    m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | m1_connsp_2(sK2,sK0,sK1)),
% 1.62/0.56    inference(cnf_transformation,[],[f29])).
% 1.62/0.56  fof(f1559,plain,(
% 1.62/0.56    ~r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))),
% 1.62/0.56    inference(resolution,[],[f525,f1540])).
% 1.62/0.56  fof(f1540,plain,(
% 1.62/0.56    ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.62/0.56    inference(subsumption_resolution,[],[f1539,f673])).
% 1.62/0.56  fof(f673,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)),
% 1.62/0.56    inference(subsumption_resolution,[],[f672,f37])).
% 1.62/0.56  fof(f672,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f671,f38])).
% 1.62/0.56  fof(f671,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f670,f39])).
% 1.62/0.56  fof(f670,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f669,f40])).
% 1.62/0.56  fof(f669,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f662,f192])).
% 1.62/0.56  fof(f192,plain,(
% 1.62/0.56    ( ! [X2] : (m1_subset_1(k3_xboole_0(sK2,X2),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.62/0.56    inference(resolution,[],[f113,f52])).
% 1.62/0.56  fof(f52,plain,(
% 1.62/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.62/0.56    inference(cnf_transformation,[],[f31])).
% 1.62/0.56  fof(f31,plain,(
% 1.62/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.62/0.56    inference(nnf_transformation,[],[f4])).
% 1.62/0.56  fof(f4,axiom,(
% 1.62/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.62/0.56  fof(f113,plain,(
% 1.62/0.56    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,X0),u1_struct_0(sK0))) )),
% 1.62/0.56    inference(resolution,[],[f103,f53])).
% 1.62/0.56  fof(f53,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.62/0.56    inference(cnf_transformation,[],[f21])).
% 1.62/0.56  fof(f21,plain,(
% 1.62/0.56    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.62/0.56    inference(ennf_transformation,[],[f2])).
% 1.62/0.56  fof(f2,axiom,(
% 1.62/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.62/0.56  fof(f103,plain,(
% 1.62/0.56    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.62/0.56    inference(resolution,[],[f41,f51])).
% 1.62/0.56  fof(f51,plain,(
% 1.62/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.62/0.56    inference(cnf_transformation,[],[f31])).
% 1.62/0.56  fof(f662,plain,(
% 1.62/0.56    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(resolution,[],[f635,f47])).
% 1.62/0.56  fof(f47,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.62/0.56    inference(cnf_transformation,[],[f30])).
% 1.62/0.56  fof(f1539,plain,(
% 1.62/0.56    ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.62/0.56    inference(subsumption_resolution,[],[f1530,f635])).
% 1.62/0.56  fof(f1530,plain,(
% 1.62/0.56    ~r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) | ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.62/0.56    inference(resolution,[],[f524,f268])).
% 1.62/0.56  fof(f268,plain,(
% 1.62/0.56    ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.62/0.56    inference(subsumption_resolution,[],[f266,f41])).
% 1.62/0.56  fof(f266,plain,(
% 1.62/0.56    ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.56    inference(resolution,[],[f156,f96])).
% 1.62/0.56  fof(f96,plain,(
% 1.62/0.56    ( ! [X2] : (m1_connsp_2(X2,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f95,f37])).
% 1.62/0.56  fof(f95,plain,(
% 1.62/0.56    ( ! [X2] : (m1_connsp_2(X2,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f94,f38])).
% 1.62/0.56  fof(f94,plain,(
% 1.62/0.56    ( ! [X2] : (m1_connsp_2(X2,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f86,f39])).
% 1.62/0.57  fof(f86,plain,(
% 1.62/0.57    ( ! [X2] : (m1_connsp_2(X2,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.62/0.57    inference(resolution,[],[f40,f47])).
% 1.62/0.57  fof(f156,plain,(
% 1.62/0.57    ~m1_connsp_2(sK2,sK0,sK1) | ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK3))),
% 1.62/0.57    inference(subsumption_resolution,[],[f155,f37])).
% 1.62/0.57  fof(f155,plain,(
% 1.62/0.57    ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | v2_struct_0(sK0)),
% 1.62/0.57    inference(subsumption_resolution,[],[f154,f38])).
% 1.62/0.57  fof(f154,plain,(
% 1.62/0.57    ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.57    inference(subsumption_resolution,[],[f153,f39])).
% 1.62/0.57  fof(f153,plain,(
% 1.62/0.57    ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.57    inference(subsumption_resolution,[],[f152,f40])).
% 1.62/0.57  fof(f152,plain,(
% 1.62/0.57    ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.57    inference(subsumption_resolution,[],[f151,f42])).
% 1.62/0.57  fof(f151,plain,(
% 1.62/0.57    ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.57    inference(resolution,[],[f133,f47])).
% 1.62/0.57  fof(f133,plain,(
% 1.62/0.57    ~m1_connsp_2(sK3,sK0,sK1) | ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)),
% 1.62/0.57    inference(backward_demodulation,[],[f45,f120])).
% 1.62/0.57  fof(f45,plain,(
% 1.62/0.57    ~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK3,sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)),
% 1.62/0.57    inference(cnf_transformation,[],[f29])).
% 1.62/0.57  fof(f524,plain,(
% 1.62/0.57    ( ! [X5] : (r2_hidden(X5,k1_tops_1(sK0,sK3)) | ~r2_hidden(X5,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))) )),
% 1.62/0.57    inference(superposition,[],[f62,f308])).
% 1.62/0.57  fof(f62,plain,(
% 1.62/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.62/0.57    inference(equality_resolution,[],[f56])).
% 1.62/0.57  fof(f56,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.62/0.57    inference(cnf_transformation,[],[f36])).
% 1.62/0.57  fof(f525,plain,(
% 1.62/0.57    ( ! [X6] : (r2_hidden(X6,k1_tops_1(sK0,sK2)) | ~r2_hidden(X6,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))) )),
% 1.62/0.57    inference(superposition,[],[f63,f308])).
% 1.62/0.57  fof(f63,plain,(
% 1.62/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.62/0.57    inference(equality_resolution,[],[f55])).
% 1.62/0.57  fof(f55,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.62/0.57    inference(cnf_transformation,[],[f36])).
% 1.62/0.57  % SZS output end Proof for theBenchmark
% 1.62/0.57  % (13353)------------------------------
% 1.62/0.57  % (13353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (13353)Termination reason: Refutation
% 1.62/0.57  
% 1.62/0.57  % (13353)Memory used [KB]: 2814
% 1.62/0.57  % (13353)Time elapsed: 0.152 s
% 1.62/0.58  % (13353)------------------------------
% 1.62/0.58  % (13353)------------------------------
% 1.62/0.58  % (13348)Success in time 0.233 s
%------------------------------------------------------------------------------
