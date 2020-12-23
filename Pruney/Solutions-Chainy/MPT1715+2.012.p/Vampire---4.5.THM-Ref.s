%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 567 expanded)
%              Number of leaves         :   18 ( 191 expanded)
%              Depth                    :   21
%              Number of atoms          :  498 (4666 expanded)
%              Number of equality atoms :   34 (  76 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(subsumption_resolution,[],[f165,f45])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_tsep_1(sK5,sK3)
      | ~ r1_tsep_1(sK3,sK5) )
    & ( r1_tsep_1(sK5,sK4)
      | r1_tsep_1(sK4,sK5) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK5,sK2)
    & m1_pre_topc(sK4,sK2)
    & m1_pre_topc(sK3,sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f14,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK2) )
              & m1_pre_topc(X2,sK2) )
          & m1_pre_topc(X1,sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK2) )
            & m1_pre_topc(X2,sK2) )
        & m1_pre_topc(X1,sK2) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r1_tsep_1(X3,sK3)
                | ~ r1_tsep_1(sK3,X3) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & m1_pre_topc(sK3,X2)
              & m1_pre_topc(X3,sK2) )
          & m1_pre_topc(X2,sK2) )
      & m1_pre_topc(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r1_tsep_1(X3,sK3)
              | ~ r1_tsep_1(sK3,X3) )
            & ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & m1_pre_topc(sK3,X2)
            & m1_pre_topc(X3,sK2) )
        & m1_pre_topc(X2,sK2) )
   => ( ? [X3] :
          ( ( ~ r1_tsep_1(X3,sK3)
            | ~ r1_tsep_1(sK3,X3) )
          & ( r1_tsep_1(X3,sK4)
            | r1_tsep_1(sK4,X3) )
          & m1_pre_topc(sK3,sK4)
          & m1_pre_topc(X3,sK2) )
      & m1_pre_topc(sK4,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ( ~ r1_tsep_1(X3,sK3)
          | ~ r1_tsep_1(sK3,X3) )
        & ( r1_tsep_1(X3,sK4)
          | r1_tsep_1(sK4,X3) )
        & m1_pre_topc(sK3,sK4)
        & m1_pre_topc(X3,sK2) )
   => ( ( ~ r1_tsep_1(sK5,sK3)
        | ~ r1_tsep_1(sK3,sK5) )
      & ( r1_tsep_1(sK5,sK4)
        | r1_tsep_1(sK4,sK5) )
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f165,plain,(
    ~ m1_pre_topc(sK3,sK4) ),
    inference(subsumption_resolution,[],[f162,f77])).

fof(f77,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f73,f41])).

fof(f41,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f65,f43])).

fof(f43,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f162,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ m1_pre_topc(sK3,sK4) ),
    inference(resolution,[],[f155,f151])).

fof(f151,plain,(
    r1_tsep_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f150,f77])).

fof(f150,plain,
    ( ~ l1_pre_topc(sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f147,f45])).

fof(f147,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(resolution,[],[f140,f46])).

fof(f46,plain,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f140,plain,(
    ! [X2] :
      ( ~ r1_tsep_1(sK5,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f139,f81])).

fof(f81,plain,(
    l1_struct_0(sK5) ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f78,plain,(
    l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f74,f41])).

fof(f74,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f139,plain,(
    ! [X2] :
      ( ~ l1_struct_0(sK5)
      | ~ r1_tsep_1(sK5,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f136,f79])).

fof(f79,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f76,f51])).

fof(f76,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f72,f41])).

fof(f72,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f65,f42])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f136,plain,(
    ! [X2] :
      ( ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK5)
      | ~ r1_tsep_1(sK5,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f133,f91])).

fof(f91,plain,(
    ~ r1_tsep_1(sK3,sK5) ),
    inference(subsumption_resolution,[],[f90,f79])).

fof(f90,plain,
    ( ~ r1_tsep_1(sK3,sK5)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f89,f81])).

fof(f89,plain,
    ( ~ r1_tsep_1(sK3,sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( ~ r1_tsep_1(sK3,sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | ~ r1_tsep_1(sK3,sK5) ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,
    ( ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X0,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f132,f51])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X1,X2)
      | ~ l1_struct_0(X2)
      | ~ m1_pre_topc(X0,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f128,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f84,f65])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | sP0(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f24,f23])).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X2)
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X2)
      | ~ l1_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X1,X0)
      | ~ sP0(X1,X2)
      | ~ r1_tsep_1(X0,X2)
      | ~ l1_struct_0(X2)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f118,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X1),k2_struct_0(X0))
      | ~ r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X1),k2_struct_0(X0))
      | ~ r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f49,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f118,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(u1_struct_0(X3),k2_struct_0(X4))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X2)
      | r1_tsep_1(X2,X3)
      | ~ sP0(X2,X4) ) ),
    inference(resolution,[],[f106,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_struct_0(X0),X1)
      | ~ r1_xboole_0(X1,k2_struct_0(X2))
      | ~ sP0(X0,X2) ) ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK6(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK6(X0,X1),u1_pre_topc(X0)) )
          & ( ( sK6(X0,X1) = k9_subset_1(u1_struct_0(X0),sK7(X0,X1),k2_struct_0(X0))
              & r2_hidden(sK7(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK6(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK8(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK8(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK8(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f35,f38,f37,f36])).

fof(f36,plain,(
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
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK6(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK6(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK6(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK6(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK6(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK6(X0,X1) = k9_subset_1(u1_struct_0(X0),sK7(X0,X1),k2_struct_0(X0))
        & r2_hidden(sK7(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

% (2840)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f38,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK8(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK8(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK8(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_xboole_0(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f69,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

% (2826)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (2823)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (2831)Refutation not found, incomplete strategy% (2831)------------------------------
% (2831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f50,f48])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f155,plain,(
    ! [X2] :
      ( ~ r1_tsep_1(X2,sK5)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(sK3,X2) ) ),
    inference(subsumption_resolution,[],[f154,f51])).

fof(f154,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(X2)
      | ~ r1_tsep_1(X2,sK5)
      | ~ l1_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f149,f81])).

fof(f149,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(X2)
      | ~ r1_tsep_1(X2,sK5)
      | ~ l1_struct_0(sK5)
      | ~ l1_struct_0(X2) ) ),
    inference(resolution,[],[f140,f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:28:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (2821)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (2828)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (2835)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (2825)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (2836)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (2821)Refutation not found, incomplete strategy% (2821)------------------------------
% 0.22/0.49  % (2821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (2821)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (2821)Memory used [KB]: 10618
% 0.22/0.49  % (2821)Time elapsed: 0.057 s
% 0.22/0.49  % (2821)------------------------------
% 0.22/0.49  % (2821)------------------------------
% 0.22/0.49  % (2822)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (2831)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (2839)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (2839)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (2830)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f165,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    m1_pre_topc(sK3,sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ((((~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)) & (r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2)) & m1_pre_topc(sK4,sK2)) & m1_pre_topc(sK3,sK2)) & l1_pre_topc(sK2)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f14,f29,f28,f27,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2)) & m1_pre_topc(X2,sK2)) & m1_pre_topc(X1,sK2)) & l1_pre_topc(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2)) & m1_pre_topc(X2,sK2)) & m1_pre_topc(X1,sK2)) => (? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2)) & m1_pre_topc(X2,sK2)) & m1_pre_topc(sK3,sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2)) & m1_pre_topc(X2,sK2)) => (? [X3] : ((~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & (r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2)) & m1_pre_topc(sK4,sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ? [X3] : ((~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & (r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2)) => ((~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)) & (r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    ~m1_pre_topc(sK3,sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f162,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    l1_pre_topc(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f73,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    l1_pre_topc(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    l1_pre_topc(sK4) | ~l1_pre_topc(sK2)),
% 0.22/0.50    inference(resolution,[],[f65,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    m1_pre_topc(sK4,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ~l1_pre_topc(sK4) | ~m1_pre_topc(sK3,sK4)),
% 0.22/0.50    inference(resolution,[],[f155,f151])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    r1_tsep_1(sK4,sK5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f150,f77])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ~l1_pre_topc(sK4) | r1_tsep_1(sK4,sK5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f147,f45])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ~m1_pre_topc(sK3,sK4) | ~l1_pre_topc(sK4) | r1_tsep_1(sK4,sK5)),
% 0.22/0.50    inference(resolution,[],[f140,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    ( ! [X2] : (~r1_tsep_1(sK5,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f139,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    l1_struct_0(sK5)),
% 0.22/0.50    inference(resolution,[],[f78,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    l1_pre_topc(sK5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f74,f41])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    l1_pre_topc(sK5) | ~l1_pre_topc(sK2)),
% 0.22/0.50    inference(resolution,[],[f65,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    m1_pre_topc(sK5,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    ( ! [X2] : (~l1_struct_0(sK5) | ~r1_tsep_1(sK5,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f136,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    l1_struct_0(sK3)),
% 0.22/0.50    inference(resolution,[],[f76,f51])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    l1_pre_topc(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f72,f41])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    l1_pre_topc(sK3) | ~l1_pre_topc(sK2)),
% 0.22/0.50    inference(resolution,[],[f65,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    m1_pre_topc(sK3,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ( ! [X2] : (~l1_struct_0(sK3) | ~l1_struct_0(sK5) | ~r1_tsep_1(sK5,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X2)) )),
% 0.22/0.50    inference(resolution,[],[f133,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ~r1_tsep_1(sK3,sK5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f90,f79])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ~r1_tsep_1(sK3,sK5) | ~l1_struct_0(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f89,f81])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ~r1_tsep_1(sK3,sK5) | ~l1_struct_0(sK5) | ~l1_struct_0(sK3)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ~r1_tsep_1(sK3,sK5) | ~l1_struct_0(sK5) | ~l1_struct_0(sK3) | ~r1_tsep_1(sK3,sK5)),
% 0.22/0.50    inference(resolution,[],[f66,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tsep_1(X0,X1) | ~l1_struct_0(X0) | ~l1_struct_0(X1) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f132,f51])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~r1_tsep_1(X1,X2) | ~l1_struct_0(X2) | ~m1_pre_topc(X0,X2) | ~l1_pre_topc(X2)) )),
% 0.22/0.50    inference(resolution,[],[f128,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sP0(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f65])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | sP0(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 0.22/0.50    inference(resolution,[],[f52,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(definition_folding,[],[f18,f24,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | ~m1_pre_topc(X1,X0) | sP0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f24])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~sP0(X1,X2) | ~l1_struct_0(X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X2) | ~l1_struct_0(X2)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~l1_struct_0(X1) | r1_tsep_1(X1,X0) | ~sP0(X1,X2) | ~r1_tsep_1(X0,X2) | ~l1_struct_0(X2) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(resolution,[],[f118,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X1),k2_struct_0(X0)) | ~r1_tsep_1(X1,X0) | ~l1_struct_0(X0) | ~l1_struct_0(X1)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X1),k2_struct_0(X0)) | ~r1_tsep_1(X1,X0) | ~l1_struct_0(X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(superposition,[],[f49,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ( ! [X4,X2,X3] : (~r1_xboole_0(u1_struct_0(X3),k2_struct_0(X4)) | ~l1_struct_0(X3) | ~l1_struct_0(X2) | r1_tsep_1(X2,X3) | ~sP0(X2,X4)) )),
% 0.22/0.50    inference(resolution,[],[f106,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(k2_struct_0(X0),X1) | ~r1_xboole_0(X1,k2_struct_0(X2)) | ~sP0(X0,X2)) )),
% 0.22/0.50    inference(resolution,[],[f83,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK6(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK6(X0,X1),u1_pre_topc(X0))) & ((sK6(X0,X1) = k9_subset_1(u1_struct_0(X0),sK7(X0,X1),k2_struct_0(X0)) & r2_hidden(sK7(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK6(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & ((k9_subset_1(u1_struct_0(X0),sK8(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK8(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK8(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f35,f38,f37,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK6(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(sK6(X0,X1),u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK6(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(sK6(X0,X1),u1_pre_topc(X0))) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK6(X0,X1) & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (sK6(X0,X1) = k9_subset_1(u1_struct_0(X0),sK7(X0,X1),k2_struct_0(X0)) & r2_hidden(sK7(X0,X1),u1_pre_topc(X1)) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  % (2840)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X0),sK8(X0,X1,X5),k2_struct_0(X0)) = X5 & r2_hidden(sK8(X0,X1,X5),u1_pre_topc(X1)) & m1_subset_1(sK8(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2 | ~r2_hidden(X3,u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X2,u1_pre_topc(X0))) & (? [X4] : (k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2 & r2_hidden(X4,u1_pre_topc(X1)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | r2_hidden(X2,u1_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X0)) | ! [X6] : (k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5 | ~r2_hidden(X6,u1_pre_topc(X1)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))))) & (? [X7] : (k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5 & r2_hidden(X7,u1_pre_topc(X1)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))) | ~r2_hidden(X5,u1_pre_topc(X0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 0.22/0.50    inference(flattening,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP0(X1,X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f23])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_xboole_0(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(superposition,[],[f69,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.50  % (2826)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (2823)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (2831)Refutation not found, incomplete strategy% (2831)------------------------------
% 0.22/0.50  % (2831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(k2_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(k2_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(superposition,[],[f50,f48])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    ( ! [X2] : (~r1_tsep_1(X2,sK5) | ~l1_pre_topc(X2) | ~m1_pre_topc(sK3,X2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f154,f51])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X2) | ~r1_tsep_1(X2,sK5) | ~l1_struct_0(X2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f149,f81])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X2) | ~r1_tsep_1(X2,sK5) | ~l1_struct_0(sK5) | ~l1_struct_0(X2)) )),
% 0.22/0.50    inference(resolution,[],[f140,f66])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (2839)------------------------------
% 0.22/0.50  % (2839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (2839)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (2839)Memory used [KB]: 1663
% 0.22/0.50  % (2839)Time elapsed: 0.078 s
% 0.22/0.50  % (2839)------------------------------
% 0.22/0.50  % (2839)------------------------------
% 0.22/0.50  % (2833)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (2817)Success in time 0.137 s
%------------------------------------------------------------------------------
