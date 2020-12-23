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
% DateTime   : Thu Dec  3 12:57:26 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 198 expanded)
%              Number of leaves         :   22 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  304 ( 894 expanded)
%              Number of equality atoms :   21 (  51 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f185,f236])).

fof(f236,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f234,f228])).

fof(f228,plain,
    ( r2_hidden(sK10(sK2,sK3),k1_relat_1(sK2))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f222,f60])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f222,plain,
    ( r2_hidden(k4_tarski(sK10(sK2,sK3),sK3),sK2)
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f190,f63])).

fof(f63,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f34,f37,f36,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f190,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f89,f94,f178,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sQ11_eqProxy(X2,X3)
      | ~ sQ11_eqProxy(X0,X1)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( sQ11_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).

fof(f178,plain,(
    sQ11_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f40,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ11_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2)) ) ),
    inference(equality_proxy_replacement,[],[f57,f64])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

% (25905)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK4,sK3),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                  | ~ m1_subset_1(X4,X1) )
              | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X3),X2)
                  & m1_subset_1(X5,X1) )
              | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
                | ~ m1_subset_1(X4,sK1) )
            | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),sK2)
                & m1_subset_1(X5,sK1) )
            | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
              | ~ m1_subset_1(X4,sK1) )
          | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X5,X3),sK2)
              & m1_subset_1(X5,sK1) )
          | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) ) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
            | ~ m1_subset_1(X4,sK1) )
        | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,sK3),sK2)
            & m1_subset_1(X5,sK1) )
        | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(X5,sK3),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK4,sK3),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(k4_tarski(X4,X3),X2)
                & m1_subset_1(X4,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
        <~> ? [X4] :
              ( r2_hidden(k4_tarski(X4,X3),X2)
              & m1_subset_1(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ! [X3] :
            ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
          <=> ? [X4] :
                ( r2_hidden(k4_tarski(X4,X3),X2)
                & m1_subset_1(X4,X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

fof(f94,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl12_1
  <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f89,plain,(
    ! [X0] : sQ11_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f64])).

fof(f234,plain,
    ( ~ r2_hidden(sK10(sK2,sK3),k1_relat_1(sK2))
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f121,f226,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

% (25898)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f226,plain,
    ( ~ m1_subset_1(sK10(sK2,sK3),sK1)
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f222,f98])).

fof(f98,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl12_2
  <=> ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f121,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f119,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f119,plain,(
    r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f113,f118,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f118,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f40,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f113,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f185,plain,
    ( spl12_1
    | ~ spl12_3 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl12_1
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f178,f173])).

fof(f173,plain,
    ( ~ sQ11_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(sK2))
    | spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f158,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ sQ11_eqProxy(X0,X1)
      | sQ11_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f64])).

fof(f158,plain,
    ( ~ sQ11_eqProxy(k2_relat_1(sK2),k2_relset_1(sK1,sK0,sK2))
    | spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f95,f124,f89,f84])).

fof(f124,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f103,f62])).

fof(f62,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl12_3
  <=> r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f95,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f104,plain,
    ( spl12_1
    | spl12_3 ),
    inference(avatar_split_clause,[],[f42,f101,f93])).

fof(f42,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f43,f97,f93])).

fof(f43,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.36  ipcrm: permission denied for id (1219166209)
% 0.21/0.36  ipcrm: permission denied for id (1223229442)
% 0.21/0.37  ipcrm: permission denied for id (1219264516)
% 0.21/0.37  ipcrm: permission denied for id (1223294981)
% 0.21/0.37  ipcrm: permission denied for id (1218772999)
% 0.21/0.37  ipcrm: permission denied for id (1219362824)
% 0.21/0.37  ipcrm: permission denied for id (1218805769)
% 0.21/0.37  ipcrm: permission denied for id (1219395594)
% 0.21/0.38  ipcrm: permission denied for id (1219428363)
% 0.21/0.38  ipcrm: permission denied for id (1219461132)
% 0.21/0.38  ipcrm: permission denied for id (1218838541)
% 0.21/0.38  ipcrm: permission denied for id (1219526670)
% 0.21/0.38  ipcrm: permission denied for id (1219559439)
% 0.21/0.38  ipcrm: permission denied for id (1223360528)
% 0.21/0.38  ipcrm: permission denied for id (1219624977)
% 0.21/0.39  ipcrm: permission denied for id (1219690515)
% 0.21/0.39  ipcrm: permission denied for id (1219756053)
% 0.21/0.39  ipcrm: permission denied for id (1223491607)
% 0.21/0.39  ipcrm: permission denied for id (1219854360)
% 0.21/0.39  ipcrm: permission denied for id (1219887129)
% 0.21/0.39  ipcrm: permission denied for id (1223557146)
% 0.21/0.39  ipcrm: permission denied for id (1223589915)
% 0.21/0.40  ipcrm: permission denied for id (1219985436)
% 0.21/0.40  ipcrm: permission denied for id (1223622685)
% 0.21/0.40  ipcrm: permission denied for id (1220050974)
% 0.21/0.40  ipcrm: permission denied for id (1220116512)
% 0.21/0.40  ipcrm: permission denied for id (1223688225)
% 0.21/0.41  ipcrm: permission denied for id (1223786532)
% 0.21/0.41  ipcrm: permission denied for id (1220280357)
% 0.21/0.41  ipcrm: permission denied for id (1220313126)
% 0.21/0.41  ipcrm: permission denied for id (1223819303)
% 0.21/0.41  ipcrm: permission denied for id (1220378664)
% 0.21/0.41  ipcrm: permission denied for id (1220411433)
% 0.21/0.41  ipcrm: permission denied for id (1220444202)
% 0.21/0.41  ipcrm: permission denied for id (1220476971)
% 0.21/0.42  ipcrm: permission denied for id (1220509740)
% 0.21/0.42  ipcrm: permission denied for id (1220542509)
% 0.21/0.42  ipcrm: permission denied for id (1220575278)
% 0.21/0.42  ipcrm: permission denied for id (1220608047)
% 0.21/0.42  ipcrm: permission denied for id (1220640816)
% 0.21/0.42  ipcrm: permission denied for id (1220706354)
% 0.21/0.42  ipcrm: permission denied for id (1220739123)
% 0.21/0.43  ipcrm: permission denied for id (1220771892)
% 0.21/0.43  ipcrm: permission denied for id (1220804661)
% 0.21/0.43  ipcrm: permission denied for id (1220837430)
% 0.21/0.43  ipcrm: permission denied for id (1220870199)
% 0.21/0.43  ipcrm: permission denied for id (1219002424)
% 0.21/0.43  ipcrm: permission denied for id (1223884857)
% 0.21/0.43  ipcrm: permission denied for id (1220935738)
% 0.21/0.43  ipcrm: permission denied for id (1220968507)
% 0.21/0.44  ipcrm: permission denied for id (1223917628)
% 0.21/0.44  ipcrm: permission denied for id (1221034045)
% 0.21/0.44  ipcrm: permission denied for id (1221066814)
% 0.21/0.44  ipcrm: permission denied for id (1223950399)
% 0.21/0.44  ipcrm: permission denied for id (1221132352)
% 0.21/0.44  ipcrm: permission denied for id (1221165121)
% 0.21/0.44  ipcrm: permission denied for id (1223983170)
% 0.21/0.44  ipcrm: permission denied for id (1221230659)
% 0.21/0.44  ipcrm: permission denied for id (1221263428)
% 0.21/0.45  ipcrm: permission denied for id (1221296197)
% 0.21/0.45  ipcrm: permission denied for id (1221328966)
% 0.21/0.45  ipcrm: permission denied for id (1224015943)
% 0.21/0.45  ipcrm: permission denied for id (1221394504)
% 0.21/0.45  ipcrm: permission denied for id (1221427273)
% 0.21/0.45  ipcrm: permission denied for id (1221460042)
% 0.21/0.45  ipcrm: permission denied for id (1221525580)
% 0.21/0.46  ipcrm: permission denied for id (1221558349)
% 0.21/0.46  ipcrm: permission denied for id (1221591118)
% 0.21/0.46  ipcrm: permission denied for id (1221623887)
% 0.21/0.46  ipcrm: permission denied for id (1221754963)
% 0.21/0.46  ipcrm: permission denied for id (1221787732)
% 0.21/0.47  ipcrm: permission denied for id (1221820501)
% 0.21/0.47  ipcrm: permission denied for id (1221853270)
% 0.21/0.47  ipcrm: permission denied for id (1221886039)
% 0.21/0.47  ipcrm: permission denied for id (1221951576)
% 0.21/0.47  ipcrm: permission denied for id (1221984345)
% 0.21/0.47  ipcrm: permission denied for id (1224278107)
% 0.21/0.48  ipcrm: permission denied for id (1222115421)
% 0.21/0.48  ipcrm: permission denied for id (1222180959)
% 0.21/0.48  ipcrm: permission denied for id (1222213728)
% 0.21/0.48  ipcrm: permission denied for id (1222246497)
% 0.21/0.48  ipcrm: permission denied for id (1224409187)
% 0.21/0.49  ipcrm: permission denied for id (1222377573)
% 0.21/0.49  ipcrm: permission denied for id (1222410342)
% 0.21/0.49  ipcrm: permission denied for id (1222475880)
% 0.21/0.49  ipcrm: permission denied for id (1222508649)
% 0.21/0.49  ipcrm: permission denied for id (1224507498)
% 0.21/0.49  ipcrm: permission denied for id (1224540267)
% 0.21/0.49  ipcrm: permission denied for id (1222606956)
% 0.21/0.50  ipcrm: permission denied for id (1222639725)
% 0.21/0.50  ipcrm: permission denied for id (1219068014)
% 0.21/0.50  ipcrm: permission denied for id (1224573039)
% 0.21/0.50  ipcrm: permission denied for id (1222705264)
% 0.21/0.50  ipcrm: permission denied for id (1224638578)
% 0.21/0.50  ipcrm: permission denied for id (1222836340)
% 0.21/0.51  ipcrm: permission denied for id (1224704117)
% 0.21/0.51  ipcrm: permission denied for id (1222934647)
% 0.21/0.51  ipcrm: permission denied for id (1222967416)
% 0.21/0.51  ipcrm: permission denied for id (1219100793)
% 0.21/0.51  ipcrm: permission denied for id (1224802427)
% 0.21/0.51  ipcrm: permission denied for id (1224835196)
% 0.21/0.52  ipcrm: permission denied for id (1223098493)
% 0.21/0.52  ipcrm: permission denied for id (1224867966)
% 0.63/0.62  % (25899)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.63/0.62  % (25909)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.63/0.63  % (25909)Refutation found. Thanks to Tanya!
% 0.63/0.63  % SZS status Theorem for theBenchmark
% 0.63/0.63  % SZS output start Proof for theBenchmark
% 0.63/0.63  fof(f237,plain,(
% 0.63/0.63    $false),
% 0.63/0.63    inference(avatar_sat_refutation,[],[f99,f104,f185,f236])).
% 0.63/0.63  fof(f236,plain,(
% 0.63/0.63    ~spl12_1 | ~spl12_2),
% 0.63/0.63    inference(avatar_contradiction_clause,[],[f235])).
% 0.63/0.63  fof(f235,plain,(
% 0.63/0.63    $false | (~spl12_1 | ~spl12_2)),
% 0.63/0.63    inference(subsumption_resolution,[],[f234,f228])).
% 0.63/0.63  fof(f228,plain,(
% 0.63/0.63    r2_hidden(sK10(sK2,sK3),k1_relat_1(sK2)) | ~spl12_1),
% 0.63/0.63    inference(unit_resulting_resolution,[],[f222,f60])).
% 0.63/0.63  fof(f60,plain,(
% 0.63/0.63    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.63/0.63    inference(equality_resolution,[],[f47])).
% 0.63/0.63  fof(f47,plain,(
% 0.63/0.63    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.63/0.63    inference(cnf_transformation,[],[f32])).
% 0.63/0.63  fof(f32,plain,(
% 0.63/0.63    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.63/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f31,f30,f29])).
% 0.63/0.63  fof(f29,plain,(
% 0.63/0.63    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.63/0.63    introduced(choice_axiom,[])).
% 0.63/0.63  fof(f30,plain,(
% 0.63/0.63    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 0.63/0.63    introduced(choice_axiom,[])).
% 0.63/0.63  fof(f31,plain,(
% 0.63/0.63    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 0.63/0.63    introduced(choice_axiom,[])).
% 0.63/0.63  fof(f28,plain,(
% 0.63/0.63    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.63/0.63    inference(rectify,[],[f27])).
% 0.63/0.63  fof(f27,plain,(
% 0.63/0.63    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.63/0.63    inference(nnf_transformation,[],[f4])).
% 0.63/0.63  fof(f4,axiom,(
% 0.63/0.63    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.63/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.63/0.63  fof(f222,plain,(
% 0.63/0.63    r2_hidden(k4_tarski(sK10(sK2,sK3),sK3),sK2) | ~spl12_1),
% 0.63/0.63    inference(unit_resulting_resolution,[],[f190,f63])).
% 0.63/0.63  fof(f63,plain,(
% 0.63/0.63    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK10(X0,X5),X5),X0)) )),
% 0.63/0.63    inference(equality_resolution,[],[f50])).
% 0.63/0.63  fof(f50,plain,(
% 0.63/0.63    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.63/0.63    inference(cnf_transformation,[],[f38])).
% 0.63/0.63  fof(f38,plain,(
% 0.63/0.63    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK8(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK10(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.63/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f34,f37,f36,f35])).
% 0.63/0.63  fof(f35,plain,(
% 0.63/0.63    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK8(X0,X1)),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0) | r2_hidden(sK8(X0,X1),X1))))),
% 0.63/0.63    introduced(choice_axiom,[])).
% 0.63/0.63  fof(f36,plain,(
% 0.63/0.63    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK8(X0,X1)),X0) => r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0))),
% 0.63/0.63    introduced(choice_axiom,[])).
% 0.63/0.63  fof(f37,plain,(
% 0.63/0.63    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK10(X0,X5),X5),X0))),
% 0.63/0.63    introduced(choice_axiom,[])).
% 0.63/0.63  fof(f34,plain,(
% 0.63/0.63    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.63/0.63    inference(rectify,[],[f33])).
% 0.63/0.63  fof(f33,plain,(
% 0.63/0.63    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.63/0.63    inference(nnf_transformation,[],[f5])).
% 0.63/0.63  fof(f5,axiom,(
% 0.63/0.63    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.63/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.63/0.63  fof(f190,plain,(
% 0.63/0.63    r2_hidden(sK3,k2_relat_1(sK2)) | ~spl12_1),
% 0.63/0.63    inference(unit_resulting_resolution,[],[f89,f94,f178,f84])).
% 0.63/0.63  fof(f84,plain,(
% 0.63/0.63    ( ! [X2,X0,X3,X1] : (~sQ11_eqProxy(X2,X3) | ~sQ11_eqProxy(X0,X1) | ~r2_hidden(X0,X2) | r2_hidden(X1,X3)) )),
% 0.63/0.63    inference(equality_proxy_axiom,[],[f64])).
% 0.63/0.63  fof(f64,plain,(
% 0.63/0.63    ! [X1,X0] : (sQ11_eqProxy(X0,X1) <=> X0 = X1)),
% 0.63/0.63    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).
% 0.63/0.63  fof(f178,plain,(
% 0.63/0.63    sQ11_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(sK2))),
% 0.63/0.63    inference(unit_resulting_resolution,[],[f40,f69])).
% 0.63/0.63  fof(f69,plain,(
% 0.63/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sQ11_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2))) )),
% 0.63/0.63    inference(equality_proxy_replacement,[],[f57,f64])).
% 0.63/0.63  fof(f57,plain,(
% 0.63/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.63/0.63    inference(cnf_transformation,[],[f16])).
% 0.63/0.63  fof(f16,plain,(
% 0.63/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.63/0.63    inference(ennf_transformation,[],[f8])).
% 0.63/0.63  % (25905)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.63/0.63  fof(f8,axiom,(
% 0.63/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.63/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.63/0.63  fof(f40,plain,(
% 0.63/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.63/0.63    inference(cnf_transformation,[],[f25])).
% 0.63/0.63  fof(f25,plain,(
% 0.63/0.63    ((! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) & ((r2_hidden(k4_tarski(sK4,sK3),sK2) & m1_subset_1(sK4,sK1)) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.63/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f24,f23,f22])).
% 0.63/0.64  fof(f22,plain,(
% 0.63/0.64    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.63/0.64    introduced(choice_axiom,[])).
% 0.63/0.64  fof(f23,plain,(
% 0.63/0.64    ? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))))),
% 0.63/0.64    introduced(choice_axiom,[])).
% 0.63/0.64  fof(f24,plain,(
% 0.63/0.64    ? [X5] : (r2_hidden(k4_tarski(X5,sK3),sK2) & m1_subset_1(X5,sK1)) => (r2_hidden(k4_tarski(sK4,sK3),sK2) & m1_subset_1(sK4,sK1))),
% 0.63/0.64    introduced(choice_axiom,[])).
% 0.63/0.64  fof(f21,plain,(
% 0.63/0.64    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.63/0.64    inference(rectify,[],[f20])).
% 0.63/0.64  fof(f20,plain,(
% 0.63/0.64    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.63/0.64    inference(nnf_transformation,[],[f13])).
% 0.63/0.64  fof(f13,plain,(
% 0.63/0.64    ? [X0,X1,X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.63/0.64    inference(ennf_transformation,[],[f11])).
% 0.63/0.64  fof(f11,plain,(
% 0.63/0.64    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))),
% 0.63/0.64    inference(pure_predicate_removal,[],[f10])).
% 0.63/0.64  fof(f10,negated_conjecture,(
% 0.63/0.64    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.63/0.64    inference(negated_conjecture,[],[f9])).
% 0.63/0.64  fof(f9,conjecture,(
% 0.63/0.64    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.63/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).
% 0.63/0.64  fof(f94,plain,(
% 0.63/0.64    r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | ~spl12_1),
% 0.63/0.64    inference(avatar_component_clause,[],[f93])).
% 0.63/0.64  fof(f93,plain,(
% 0.63/0.64    spl12_1 <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.63/0.64    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.63/0.64  fof(f89,plain,(
% 0.63/0.64    ( ! [X0] : (sQ11_eqProxy(X0,X0)) )),
% 0.63/0.64    inference(equality_proxy_axiom,[],[f64])).
% 0.63/0.64  fof(f234,plain,(
% 0.63/0.64    ~r2_hidden(sK10(sK2,sK3),k1_relat_1(sK2)) | (~spl12_1 | ~spl12_2)),
% 0.63/0.64    inference(unit_resulting_resolution,[],[f121,f226,f59])).
% 0.63/0.64  fof(f59,plain,(
% 0.63/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.63/0.64    inference(cnf_transformation,[],[f19])).
% 0.63/0.64  % (25898)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.63/0.64  fof(f19,plain,(
% 0.63/0.64    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.63/0.64    inference(flattening,[],[f18])).
% 0.63/0.64  fof(f18,plain,(
% 0.63/0.64    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.63/0.64    inference(ennf_transformation,[],[f2])).
% 0.63/0.64  fof(f2,axiom,(
% 0.63/0.64    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.63/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.63/0.64  fof(f226,plain,(
% 0.63/0.64    ~m1_subset_1(sK10(sK2,sK3),sK1) | (~spl12_1 | ~spl12_2)),
% 0.63/0.64    inference(unit_resulting_resolution,[],[f222,f98])).
% 0.63/0.64  fof(f98,plain,(
% 0.63/0.64    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl12_2),
% 0.63/0.64    inference(avatar_component_clause,[],[f97])).
% 0.63/0.64  fof(f97,plain,(
% 0.63/0.64    spl12_2 <=> ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1))),
% 0.63/0.64    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.63/0.64  fof(f121,plain,(
% 0.63/0.64    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.63/0.64    inference(unit_resulting_resolution,[],[f119,f55])).
% 0.63/0.64  fof(f55,plain,(
% 0.63/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.63/0.64    inference(cnf_transformation,[],[f39])).
% 0.63/0.64  fof(f39,plain,(
% 0.63/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.63/0.64    inference(nnf_transformation,[],[f1])).
% 0.63/0.64  fof(f1,axiom,(
% 0.63/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.63/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.63/0.64  fof(f119,plain,(
% 0.63/0.64    r1_tarski(k1_relat_1(sK2),sK1)),
% 0.63/0.64    inference(unit_resulting_resolution,[],[f113,f118,f44])).
% 0.63/0.64  fof(f44,plain,(
% 0.63/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.63/0.64    inference(cnf_transformation,[],[f26])).
% 0.63/0.64  fof(f26,plain,(
% 0.63/0.64    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.63/0.64    inference(nnf_transformation,[],[f14])).
% 0.63/0.64  fof(f14,plain,(
% 0.63/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.63/0.64    inference(ennf_transformation,[],[f3])).
% 0.63/0.64  fof(f3,axiom,(
% 0.63/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.63/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.63/0.64  fof(f118,plain,(
% 0.63/0.64    v4_relat_1(sK2,sK1)),
% 0.63/0.64    inference(unit_resulting_resolution,[],[f40,f58])).
% 0.63/0.64  fof(f58,plain,(
% 0.63/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.63/0.64    inference(cnf_transformation,[],[f17])).
% 0.63/0.64  fof(f17,plain,(
% 0.63/0.64    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.63/0.64    inference(ennf_transformation,[],[f12])).
% 0.63/0.64  fof(f12,plain,(
% 0.63/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.63/0.64    inference(pure_predicate_removal,[],[f7])).
% 0.63/0.64  fof(f7,axiom,(
% 0.63/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.63/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.63/0.64  fof(f113,plain,(
% 0.63/0.64    v1_relat_1(sK2)),
% 0.63/0.64    inference(unit_resulting_resolution,[],[f40,f56])).
% 0.63/0.64  fof(f56,plain,(
% 0.63/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.63/0.64    inference(cnf_transformation,[],[f15])).
% 0.63/0.64  fof(f15,plain,(
% 0.63/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.63/0.64    inference(ennf_transformation,[],[f6])).
% 0.63/0.64  fof(f6,axiom,(
% 0.63/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.63/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.63/0.64  fof(f185,plain,(
% 0.63/0.64    spl12_1 | ~spl12_3),
% 0.63/0.64    inference(avatar_contradiction_clause,[],[f184])).
% 0.63/0.64  fof(f184,plain,(
% 0.63/0.64    $false | (spl12_1 | ~spl12_3)),
% 0.63/0.64    inference(subsumption_resolution,[],[f178,f173])).
% 0.63/0.64  fof(f173,plain,(
% 0.63/0.64    ~sQ11_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(sK2)) | (spl12_1 | ~spl12_3)),
% 0.63/0.64    inference(unit_resulting_resolution,[],[f158,f90])).
% 0.63/0.64  fof(f90,plain,(
% 0.63/0.64    ( ! [X0,X1] : (~sQ11_eqProxy(X0,X1) | sQ11_eqProxy(X1,X0)) )),
% 0.63/0.64    inference(equality_proxy_axiom,[],[f64])).
% 0.63/0.64  fof(f158,plain,(
% 0.63/0.64    ~sQ11_eqProxy(k2_relat_1(sK2),k2_relset_1(sK1,sK0,sK2)) | (spl12_1 | ~spl12_3)),
% 0.63/0.64    inference(unit_resulting_resolution,[],[f95,f124,f89,f84])).
% 0.63/0.64  fof(f124,plain,(
% 0.63/0.64    r2_hidden(sK3,k2_relat_1(sK2)) | ~spl12_3),
% 0.63/0.64    inference(unit_resulting_resolution,[],[f103,f62])).
% 0.63/0.64  fof(f62,plain,(
% 0.63/0.64    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.63/0.64    inference(equality_resolution,[],[f51])).
% 0.63/0.64  fof(f51,plain,(
% 0.63/0.64    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.63/0.64    inference(cnf_transformation,[],[f38])).
% 0.63/0.64  fof(f103,plain,(
% 0.63/0.64    r2_hidden(k4_tarski(sK4,sK3),sK2) | ~spl12_3),
% 0.63/0.64    inference(avatar_component_clause,[],[f101])).
% 0.63/0.64  fof(f101,plain,(
% 0.63/0.64    spl12_3 <=> r2_hidden(k4_tarski(sK4,sK3),sK2)),
% 0.63/0.64    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.63/0.64  fof(f95,plain,(
% 0.63/0.64    ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | spl12_1),
% 0.63/0.64    inference(avatar_component_clause,[],[f93])).
% 0.63/0.64  fof(f104,plain,(
% 0.63/0.64    spl12_1 | spl12_3),
% 0.63/0.64    inference(avatar_split_clause,[],[f42,f101,f93])).
% 0.63/0.64  fof(f42,plain,(
% 0.63/0.64    r2_hidden(k4_tarski(sK4,sK3),sK2) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.63/0.64    inference(cnf_transformation,[],[f25])).
% 0.63/0.64  fof(f99,plain,(
% 0.63/0.64    ~spl12_1 | spl12_2),
% 0.63/0.64    inference(avatar_split_clause,[],[f43,f97,f93])).
% 0.63/0.64  fof(f43,plain,(
% 0.63/0.64    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) )),
% 0.63/0.64    inference(cnf_transformation,[],[f25])).
% 0.63/0.64  % SZS output end Proof for theBenchmark
% 0.63/0.64  % (25909)------------------------------
% 0.63/0.64  % (25909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.63/0.64  % (25909)Termination reason: Refutation
% 0.63/0.64  
% 0.63/0.64  % (25909)Memory used [KB]: 10746
% 0.63/0.64  % (25909)Time elapsed: 0.014 s
% 0.63/0.64  % (25909)------------------------------
% 0.63/0.64  % (25909)------------------------------
% 1.15/0.64  % (25756)Success in time 0.282 s
%------------------------------------------------------------------------------
