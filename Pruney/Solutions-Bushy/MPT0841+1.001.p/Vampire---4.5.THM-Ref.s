%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0841+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 369 expanded)
%              Number of leaves         :   25 ( 153 expanded)
%              Depth                    :   17
%              Number of atoms          :  514 (3468 expanded)
%              Number of equality atoms :   14 (  57 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f546,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f81,f109,f145,f253,f263,f512,f544])).

fof(f544,plain,
    ( ~ spl9_1
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f531])).

fof(f531,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_8 ),
    inference(resolution,[],[f526,f148])).

fof(f148,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f147,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
          | ~ m1_subset_1(X5,sK2) )
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
    & ( ( r2_hidden(sK5,sK1)
        & r2_hidden(k4_tarski(sK5,sK4),sK3)
        & m1_subset_1(sK5,sK2) )
      | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f23,f29,f28,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                        & m1_subset_1(X4,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X6,X4),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                      & m1_subset_1(X4,sK0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ! [X5] :
                          ( ~ r2_hidden(X5,X1)
                          | ~ r2_hidden(k4_tarski(X5,X4),X3)
                          | ~ m1_subset_1(X5,X2) )
                      | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                    & ( ? [X6] :
                          ( r2_hidden(X6,X1)
                          & r2_hidden(k4_tarski(X6,X4),X3)
                          & m1_subset_1(X6,X2) )
                      | r2_hidden(X4,k7_relset_1(X2,sK0,X3,X1)) )
                    & m1_subset_1(X4,sK0) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ! [X5] :
                        ( ~ r2_hidden(X5,sK1)
                        | ~ r2_hidden(k4_tarski(X5,X4),X3)
                        | ~ m1_subset_1(X5,X2) )
                    | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                  & ( ? [X6] :
                        ( r2_hidden(X6,sK1)
                        & r2_hidden(k4_tarski(X6,X4),X3)
                        & m1_subset_1(X6,X2) )
                    | r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ! [X5] :
                      ( ~ r2_hidden(X5,sK1)
                      | ~ r2_hidden(k4_tarski(X5,X4),X3)
                      | ~ m1_subset_1(X5,X2) )
                  | ~ r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                & ( ? [X6] :
                      ( r2_hidden(X6,sK1)
                      & r2_hidden(k4_tarski(X6,X4),X3)
                      & m1_subset_1(X6,X2) )
                  | r2_hidden(X4,k7_relset_1(X2,sK0,X3,sK1)) )
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ! [X5] :
                    ( ~ r2_hidden(X5,sK1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X3)
                    | ~ m1_subset_1(X5,sK2) )
                | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
              & ( ? [X6] :
                    ( r2_hidden(X6,sK1)
                    & r2_hidden(k4_tarski(X6,X4),X3)
                    & m1_subset_1(X6,sK2) )
                | r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,sK1)
                  | ~ r2_hidden(k4_tarski(X5,X4),X3)
                  | ~ m1_subset_1(X5,sK2) )
              | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,sK1)
                  & r2_hidden(k4_tarski(X6,X4),X3)
                  & m1_subset_1(X6,sK2) )
              | r2_hidden(X4,k7_relset_1(sK2,sK0,X3,sK1)) )
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK1)
                | ~ r2_hidden(k4_tarski(X5,X4),sK3)
                | ~ m1_subset_1(X5,sK2) )
            | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK1)
                & r2_hidden(k4_tarski(X6,X4),sK3)
                & m1_subset_1(X6,sK2) )
            | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X4] :
        ( ( ! [X5] :
              ( ~ r2_hidden(X5,sK1)
              | ~ r2_hidden(k4_tarski(X5,X4),sK3)
              | ~ m1_subset_1(X5,sK2) )
          | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,sK1)
              & r2_hidden(k4_tarski(X6,X4),sK3)
              & m1_subset_1(X6,sK2) )
          | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
        & m1_subset_1(X4,sK0) )
   => ( ( ! [X5] :
            ( ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
            | ~ m1_subset_1(X5,sK2) )
        | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
      & ( ? [X6] :
            ( r2_hidden(X6,sK1)
            & r2_hidden(k4_tarski(X6,sK4),sK3)
            & m1_subset_1(X6,sK2) )
        | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(X6,sK4),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK5,sK4),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & ( ? [X6] :
                            ( r2_hidden(X6,X1)
                            & r2_hidden(k4_tarski(X6,X4),X3)
                            & m1_subset_1(X6,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(X5,X1)
                            | ~ r2_hidden(k4_tarski(X5,X4),X3)
                            | ~ m1_subset_1(X5,X2) )
                        | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) )
                        | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(f147,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl9_1 ),
    inference(superposition,[],[f73,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f73,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl9_1
  <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f526,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k9_relat_1(sK3,X1))
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f513,f101])).

fof(f101,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f42])).

% (5393)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f513,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ v1_relat_1(sK3) )
    | ~ spl9_8 ),
    inference(resolution,[],[f105,f65])).

fof(f65,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

% (5407)Refutation not found, incomplete strategy% (5407)------------------------------
% (5407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5407)Termination reason: Refutation not found, incomplete strategy

% (5407)Memory used [KB]: 10618
% (5407)Time elapsed: 0.098 s
% (5407)------------------------------
% (5407)------------------------------
fof(f48,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f32,f35,f34,f33])).

% (5399)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f105,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl9_8
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f512,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_13 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f509,f148])).

fof(f509,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_13 ),
    inference(resolution,[],[f389,f162])).

fof(f162,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f161,f101])).

fof(f161,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f160,f148])).

fof(f160,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl9_2 ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK4),sK2)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f154,f64])).

fof(f64,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK3,X0,sK4),sK1)
        | ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f150,f101])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK3,X0,sK4),sK2)
        | ~ r2_hidden(sK8(sK3,X0,sK4),sK1)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ v1_relat_1(sK3) )
    | ~ spl9_2 ),
    inference(resolution,[],[f71,f65])).

fof(f71,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(X5,sK4),sK3)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl9_2
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(k4_tarski(X5,sK4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f389,plain,
    ( ! [X4,X5] :
        ( m1_subset_1(sK8(sK3,X5,X4),sK2)
        | ~ r2_hidden(X4,k9_relat_1(sK3,X5)) )
    | ~ spl9_13 ),
    inference(resolution,[],[f315,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f315,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK8(sK3,X0,X1),sK2)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f313,f101])).

fof(f313,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK8(sK3,X0,X1),sK2)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | ~ v1_relat_1(sK3) )
    | ~ spl9_13 ),
    inference(resolution,[],[f271,f65])).

fof(f271,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK3)
        | r2_hidden(X3,sK2) )
    | ~ spl9_13 ),
    inference(resolution,[],[f252,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f252,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK2,sK0))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl9_13
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k2_zfmisc_1(sK2,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f263,plain,
    ( ~ spl9_4
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(resolution,[],[f105,f80])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl9_4
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f253,plain,
    ( spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f140,f251,f107])).

fof(f107,plain,
    ( spl9_9
  <=> v1_xboole_0(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | v1_xboole_0(k2_zfmisc_1(sK2,sK0))
      | r2_hidden(X0,k2_zfmisc_1(sK2,sK0)) ) ),
    inference(resolution,[],[f110,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f110,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(sK2,sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f57,f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f145,plain,
    ( spl9_1
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f142,f76])).

fof(f76,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl9_3
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f142,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f121,f118])).

fof(f118,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f117,f42])).

fof(f117,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | spl9_1 ),
    inference(superposition,[],[f68,f59])).

fof(f68,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f121,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK5,X0) )
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f119,f101])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ v1_relat_1(sK3) )
    | ~ spl9_4 ),
    inference(resolution,[],[f63,f80])).

fof(f63,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ r2_hidden(X7,X1)
      | r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f109,plain,
    ( spl9_8
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f102,f107,f104])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

% (5398)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f81,plain,
    ( spl9_1
    | spl9_4 ),
    inference(avatar_split_clause,[],[f45,f79,f67])).

fof(f45,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f46,f75,f67])).

fof(f46,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f47,f70,f67])).

fof(f47,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
