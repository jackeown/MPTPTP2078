%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t12_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:06 EDT 2019

% Result     : Theorem 154.67s
% Output     : Refutation 154.67s
% Verified   : 
% Statistics : Number of formulae       :  175 (4041 expanded)
%              Number of leaves         :   23 (1195 expanded)
%              Depth                    :   30
%              Number of atoms          :  622 (26497 expanded)
%              Number of equality atoms :  114 (3988 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229080,plain,(
    $false ),
    inference(subsumption_resolution,[],[f229079,f144812])).

fof(f144812,plain,(
    r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f144799,f4260])).

fof(f4260,plain,
    ( r2_hidden(sK6(sK4,sK2),u1_pre_topc(sK2))
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f4259,f845])).

fof(f845,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f844,f204])).

fof(f204,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f163,f104])).

fof(f104,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',d3_struct_0)).

fof(f163,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f97,f107])).

fof(f107,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',dt_l1_pre_topc)).

fof(f97,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,
    ( ( ~ m1_pre_topc(sK4,sK2)
      | ~ m1_pre_topc(sK3,sK2) )
    & ( m1_pre_topc(sK4,sK2)
      | m1_pre_topc(sK3,sK2) )
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK3
    & l1_pre_topc(sK4)
    & l1_pre_topc(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f74,f77,f76,f75])).

fof(f75,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) )
                & ( m1_pre_topc(X2,X0)
                  | m1_pre_topc(X1,X0) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
                & l1_pre_topc(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK2)
                | ~ m1_pre_topc(X1,sK2) )
              & ( m1_pre_topc(X2,sK2)
                | m1_pre_topc(X1,sK2) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ m1_pre_topc(X1,X0) )
              & ( m1_pre_topc(X2,X0)
                | m1_pre_topc(X1,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(sK3,X0) )
            & ( m1_pre_topc(X2,X0)
              | m1_pre_topc(sK3,X0) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3
            & l1_pre_topc(X2) )
        & l1_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,X0)
            | ~ m1_pre_topc(X1,X0) )
          & ( m1_pre_topc(X2,X0)
            | m1_pre_topc(X1,X0) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
          & l1_pre_topc(X2) )
     => ( ( ~ m1_pre_topc(sK4,X0)
          | ~ m1_pre_topc(X1,X0) )
        & ( m1_pre_topc(sK4,X0)
          | m1_pre_topc(X1,X0) )
        & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X1
        & l1_pre_topc(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ m1_pre_topc(X1,X0) )
              & ( m1_pre_topc(X2,X0)
                | m1_pre_topc(X1,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ m1_pre_topc(X1,X0) )
              & ( m1_pre_topc(X2,X0)
                | m1_pre_topc(X1,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_pre_topc(X1,X0)
              <~> m1_pre_topc(X2,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_pre_topc(X1,X0)
              <~> m1_pre_topc(X2,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( l1_pre_topc(X2)
               => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
                 => ( m1_pre_topc(X1,X0)
                  <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
                 => ( m1_pre_topc(X1,X0)
                  <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',t12_tmap_1)).

fof(f844,plain,(
    r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f838,f190])).

fof(f190,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f154,f104])).

fof(f154,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f96,f107])).

fof(f96,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f838,plain,(
    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(resolution,[],[f818,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK5(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1),k2_struct_0(X0)) = sK5(X0,X1)
              & r2_hidden(sK6(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK7(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK7(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK7(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f82,f85,f84,f83])).

fof(f83,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,u1_pre_topc(X0)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                & r2_hidden(X4,u1_pre_topc(X1))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,u1_pre_topc(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK5(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK5(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK6(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK7(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK7(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK7(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,u1_pre_topc(X0)) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                  & r2_hidden(X4,u1_pre_topc(X1))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,u1_pre_topc(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ? [X7] :
                      ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
                      & r2_hidden(X7,u1_pre_topc(X1))
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X0))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,u1_pre_topc(X1)) )
            & ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,u1_pre_topc(X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & r2_hidden(X3,u1_pre_topc(X0))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( ( r2_hidden(X2,u1_pre_topc(X1))
            <=> ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f818,plain,(
    sP0(sK3,sK2) ),
    inference(resolution,[],[f816,f350])).

fof(f350,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f348,f96])).

fof(f348,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f193,f100])).

fof(f100,plain,
    ( m1_pre_topc(sK4,sK2)
    | m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f193,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK4,X1)
      | m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f125,f99])).

fof(f99,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK3 ),
    inference(cnf_transformation,[],[f78])).

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',t11_tmap_1)).

fof(f816,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | sP0(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f228,f159])).

fof(f159,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | l1_pre_topc(X2) ) ),
    inference(resolution,[],[f96,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',dt_m1_pre_topc)).

fof(f228,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | sP0(X0,sK2)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(resolution,[],[f157,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f157,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f96,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f51,f71,f70])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',d9_pre_topc)).

fof(f4259,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
    | r2_hidden(sK6(sK4,sK2),u1_pre_topc(sK2)) ),
    inference(forward_demodulation,[],[f4258,f563])).

fof(f563,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK4) ),
    inference(backward_demodulation,[],[f461,f206])).

fof(f206,plain,(
    u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(resolution,[],[f172,f104])).

fof(f172,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f98,f107])).

fof(f98,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f461,plain,(
    u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f458,f164])).

fof(f164,plain,(
    m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(resolution,[],[f97,f108])).

fof(f108,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',dt_u1_pre_topc)).

fof(f458,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(trivial_inequality_removal,[],[f456])).

fof(f456,plain,
    ( sK3 != sK3
    | u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(superposition,[],[f195,f367])).

fof(f367,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
    inference(subsumption_resolution,[],[f165,f338])).

fof(f338,plain,(
    v1_pre_topc(sK3) ),
    inference(forward_demodulation,[],[f325,f99])).

fof(f325,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(resolution,[],[f173,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',dt_g1_pre_topc)).

fof(f173,plain,(
    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(resolution,[],[f98,f108])).

fof(f165,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | ~ v1_pre_topc(sK3) ),
    inference(resolution,[],[f97,f109])).

fof(f109,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',abstractness_v1_pre_topc)).

fof(f195,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != sK3
      | u1_struct_0(sK4) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f135,f99])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',free_g1_pre_topc)).

fof(f4258,plain,
    ( ~ r1_tarski(k2_struct_0(sK4),u1_struct_0(sK2))
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
    | r2_hidden(sK6(sK4,sK2),u1_pre_topc(sK2)) ),
    inference(forward_demodulation,[],[f4257,f190])).

fof(f4257,plain,
    ( r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
    | r2_hidden(sK6(sK4,sK2),u1_pre_topc(sK2))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f412,f469])).

fof(f469,plain,(
    u1_pre_topc(sK3) = u1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f466,f164])).

fof(f466,plain,
    ( u1_pre_topc(sK3) = u1_pre_topc(sK4)
    | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(trivial_inequality_removal,[],[f464])).

fof(f464,plain,
    ( sK3 != sK3
    | u1_pre_topc(sK3) = u1_pre_topc(sK4)
    | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(superposition,[],[f197,f367])).

fof(f197,plain,(
    ! [X6,X7] :
      ( g1_pre_topc(X6,X7) != sK3
      | u1_pre_topc(sK4) = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))) ) ),
    inference(superposition,[],[f136,f99])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f412,plain,
    ( r2_hidden(sK6(sK4,sK2),u1_pre_topc(sK2))
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ),
    inference(resolution,[],[f406,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK6(X0,X1),u1_pre_topc(X1))
      | r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f406,plain,(
    ~ sP0(sK4,sK2) ),
    inference(subsumption_resolution,[],[f402,f98])).

fof(f402,plain,
    ( ~ sP0(sK4,sK2)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f401,f157])).

fof(f401,plain,
    ( ~ sP1(sK2,sK4)
    | ~ sP0(sK4,sK2) ),
    inference(subsumption_resolution,[],[f188,f350])).

fof(f188,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ sP0(sK4,sK2)
    | ~ sP1(sK2,sK4) ),
    inference(resolution,[],[f101,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f101,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f78])).

fof(f144799,plain,
    ( r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
    | ~ r2_hidden(sK6(sK4,sK2),u1_pre_topc(sK2)) ),
    inference(duplicate_literal_removal,[],[f144767])).

fof(f144767,plain,
    ( r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
    | ~ r2_hidden(sK6(sK4,sK2),u1_pre_topc(sK2))
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3)) ),
    inference(superposition,[],[f13816,f6290])).

fof(f6290,plain,
    ( k3_xboole_0(u1_struct_0(sK3),sK6(sK4,sK2)) = sK5(sK4,sK2)
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f6289,f845])).

fof(f6289,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
    | k3_xboole_0(u1_struct_0(sK3),sK6(sK4,sK2)) = sK5(sK4,sK2) ),
    inference(forward_demodulation,[],[f6288,f563])).

fof(f6288,plain,
    ( ~ r1_tarski(k2_struct_0(sK4),u1_struct_0(sK2))
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
    | k3_xboole_0(u1_struct_0(sK3),sK6(sK4,sK2)) = sK5(sK4,sK2) ),
    inference(forward_demodulation,[],[f6287,f190])).

fof(f6287,plain,
    ( r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
    | k3_xboole_0(u1_struct_0(sK3),sK6(sK4,sK2)) = sK5(sK4,sK2)
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f6286,f469])).

fof(f6286,plain,
    ( k3_xboole_0(u1_struct_0(sK3),sK6(sK4,sK2)) = sK5(sK4,sK2)
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f6285,f129])).

fof(f129,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',commutativity_k3_xboole_0)).

fof(f6285,plain,
    ( k3_xboole_0(sK6(sK4,sK2),u1_struct_0(sK3)) = sK5(sK4,sK2)
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f6284,f772])).

fof(f772,plain,(
    ! [X6] : k3_xboole_0(X6,u1_struct_0(sK3)) = k9_subset_1(u1_struct_0(sK3),X6,u1_struct_0(sK3)) ),
    inference(resolution,[],[f722,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',redefinition_k9_subset_1)).

fof(f722,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f203,f204])).

fof(f203,plain,(
    m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f163,f105])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',dt_k2_struct_0)).

fof(f6284,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK6(sK4,sK2),u1_struct_0(sK3)) = sK5(sK4,sK2)
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f6283,f461])).

fof(f6283,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK6(sK4,sK2),u1_struct_0(sK3)) = sK5(sK4,sK2)
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f413,f563])).

fof(f413,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK6(sK4,sK2),k2_struct_0(sK4)) = sK5(sK4,sK2)
    | r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
    | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ),
    inference(resolution,[],[f406,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),sK6(X0,X1),k2_struct_0(X0)) = sK5(X0,X1)
      | r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f13816,plain,(
    ! [X0] :
      ( r2_hidden(k3_xboole_0(u1_struct_0(sK3),X0),u1_pre_topc(sK3))
      | ~ r2_hidden(X0,u1_pre_topc(sK2)) ) ),
    inference(superposition,[],[f7430,f129])).

fof(f7430,plain,(
    ! [X3] :
      ( r2_hidden(k3_xboole_0(X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(forward_demodulation,[],[f7429,f772])).

fof(f7429,plain,(
    ! [X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(forward_demodulation,[],[f7428,f204])).

fof(f7428,plain,(
    ! [X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(subsumption_resolution,[],[f7427,f2594])).

fof(f2594,plain,(
    ! [X5] : m1_subset_1(k3_xboole_0(X5,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(backward_demodulation,[],[f772,f771])).

fof(f771,plain,(
    ! [X5] : m1_subset_1(k9_subset_1(u1_struct_0(sK3),X5,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f722,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',dt_k9_subset_1)).

fof(f7427,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k3_xboole_0(X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(forward_demodulation,[],[f7426,f772])).

fof(f7426,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(subsumption_resolution,[],[f7377,f818])).

fof(f7377,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK2))
      | ~ sP0(sK3,sK2) ) ),
    inference(superposition,[],[f1111,f204])).

fof(f1111,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X7),X6,k2_struct_0(X7)),k1_zfmisc_1(u1_struct_0(X7)))
      | r2_hidden(k9_subset_1(u1_struct_0(X7),X6,k2_struct_0(X7)),u1_pre_topc(X7))
      | ~ r2_hidden(X6,u1_pre_topc(sK2))
      | ~ sP0(X7,sK2) ) ),
    inference(duplicate_literal_removal,[],[f1099])).

fof(f1099,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,u1_pre_topc(sK2))
      | r2_hidden(k9_subset_1(u1_struct_0(X7),X6,k2_struct_0(X7)),u1_pre_topc(X7))
      | ~ r2_hidden(X6,u1_pre_topc(sK2))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X7),X6,k2_struct_0(X7)),k1_zfmisc_1(u1_struct_0(X7)))
      | ~ sP0(X7,sK2) ) ),
    inference(resolution,[],[f305,f149])).

fof(f149,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f305,plain,(
    ! [X7] :
      ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X7,u1_pre_topc(sK2)) ) ),
    inference(resolution,[],[f155,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t12_tmap_1.p',t4_subset)).

fof(f155,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f96,f108])).

fof(f229079,plain,(
    ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3)) ),
    inference(equality_resolution,[],[f229077])).

fof(f229077,plain,(
    ! [X3] :
      ( sK5(sK4,sK2) != X3
      | ~ r2_hidden(X3,u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f29609,f144812])).

fof(f29609,plain,(
    ! [X3] :
      ( sK5(sK4,sK2) != X3
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f29601,f19507])).

fof(f19507,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK3,sK2,X1),u1_pre_topc(sK2))
      | ~ r2_hidden(X1,u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f840,f317])).

fof(f317,plain,(
    ! [X7] :
      ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X7,u1_pre_topc(sK3)) ) ),
    inference(resolution,[],[f164,f145])).

fof(f840,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK3,sK2,X1),u1_pre_topc(sK2))
      | ~ r2_hidden(X1,u1_pre_topc(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f818,f114])).

fof(f114,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X1,X5),u1_pre_topc(X1))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f29601,plain,(
    ! [X3] :
      ( sK5(sK4,sK2) != X3
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
      | ~ r2_hidden(sK7(sK3,sK2,X3),u1_pre_topc(sK2))
      | ~ r2_hidden(X3,u1_pre_topc(sK3)) ) ),
    inference(superposition,[],[f8227,f29598])).

fof(f29598,plain,(
    ! [X2] :
      ( k3_xboole_0(u1_struct_0(sK3),sK7(sK3,sK2,X2)) = X2
      | ~ r2_hidden(X2,u1_pre_topc(sK3)) ) ),
    inference(forward_demodulation,[],[f29597,f129])).

fof(f29597,plain,(
    ! [X2] :
      ( k3_xboole_0(sK7(sK3,sK2,X2),u1_struct_0(sK3)) = X2
      | ~ r2_hidden(X2,u1_pre_topc(sK3)) ) ),
    inference(forward_demodulation,[],[f29596,f772])).

fof(f29596,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK3),sK7(sK3,sK2,X2),u1_struct_0(sK3)) = X2
      | ~ r2_hidden(X2,u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f846,f317])).

fof(f846,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK3),sK7(sK3,sK2,X2),u1_struct_0(sK3)) = X2
      | ~ r2_hidden(X2,u1_pre_topc(sK3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(forward_demodulation,[],[f841,f204])).

fof(f841,plain,(
    ! [X2] :
      ( k9_subset_1(u1_struct_0(sK3),sK7(sK3,sK2,X2),k2_struct_0(sK3)) = X2
      | ~ r2_hidden(X2,u1_pre_topc(sK3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f818,f115])).

fof(f115,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK7(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f8227,plain,(
    ! [X0] :
      ( k3_xboole_0(u1_struct_0(sK3),X0) != sK5(sK4,sK2)
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
      | ~ r2_hidden(X0,u1_pre_topc(sK2)) ) ),
    inference(superposition,[],[f8225,f129])).

fof(f8225,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,u1_struct_0(sK3)) != sK5(sK4,sK2)
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
      | ~ r2_hidden(X0,u1_pre_topc(sK2)) ) ),
    inference(subsumption_resolution,[],[f8224,f845])).

fof(f8224,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
      | k3_xboole_0(X0,u1_struct_0(sK3)) != sK5(sK4,sK2)
      | ~ r2_hidden(X0,u1_pre_topc(sK2)) ) ),
    inference(forward_demodulation,[],[f8223,f563])).

fof(f8223,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_struct_0(sK4),u1_struct_0(sK2))
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
      | k3_xboole_0(X0,u1_struct_0(sK3)) != sK5(sK4,sK2)
      | ~ r2_hidden(X0,u1_pre_topc(sK2)) ) ),
    inference(forward_demodulation,[],[f8222,f190])).

fof(f8222,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK3))
      | k3_xboole_0(X0,u1_struct_0(sK3)) != sK5(sK4,sK2)
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f8221,f469])).

fof(f8221,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,u1_struct_0(sK3)) != sK5(sK4,sK2)
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
      | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f8220,f772])).

fof(f8220,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK3),X0,u1_struct_0(sK3)) != sK5(sK4,sK2)
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
      | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f8219,f461])).

fof(f8219,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK4),X0,u1_struct_0(sK3)) != sK5(sK4,sK2)
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
      | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f8218,f563])).

fof(f8218,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK4),X0,k2_struct_0(sK4)) != sK5(sK4,sK2)
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
      | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f414,f305])).

fof(f414,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK4),X0,k2_struct_0(sK4)) != sK5(sK4,sK2)
      | ~ r2_hidden(X0,u1_pre_topc(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK5(sK4,sK2),u1_pre_topc(sK4))
      | ~ r1_tarski(k2_struct_0(sK4),k2_struct_0(sK2)) ) ),
    inference(resolution,[],[f406,f121])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK5(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f86])).
%------------------------------------------------------------------------------
