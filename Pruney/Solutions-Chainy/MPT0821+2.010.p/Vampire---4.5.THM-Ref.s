%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:28 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 182 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  284 ( 785 expanded)
%              Number of equality atoms :   40 ( 159 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f66,f83,f95,f106,f120])).

fof(f120,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f118,f61])).

fof(f61,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl9_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f118,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f115,f107])).

fof(f107,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f67,f55])).

fof(f55,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl9_2
  <=> sK1 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f67,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f31,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | ! [X5] :
          ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
          | ~ r2_hidden(X5,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X1,X0,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( sK1 != k1_relset_1(sK1,sK0,sK2)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK2)
            & r2_hidden(X3,sK1) ) )
      & ( sK1 = k1_relset_1(sK1,sK0,sK2)
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK2)
            | ~ r2_hidden(X5,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),sK2)
        & r2_hidden(X3,sK1) )
   => ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X5,X6),sK2)
     => r2_hidden(k4_tarski(X5,sK4(X5)),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X5,X6),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( k1_relset_1(X1,X0,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

% (5684)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f115,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f52,f49])).

fof(f49,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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

fof(f52,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl9_1
  <=> ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f106,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f101,f82])).

fof(f82,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK6(sK2,sK1),X0),sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl9_6
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK6(sK2,sK1),X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f101,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK1),sK4(sK6(sK2,sK1))),sK2)
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f78,f65])).

fof(f65,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | r2_hidden(k4_tarski(X5,sK4(X5)),sK2) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl9_4
  <=> ! [X5] :
        ( r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f78,plain,
    ( r2_hidden(sK6(sK2,sK1),sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl9_5
  <=> r2_hidden(sK6(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f95,plain,
    ( spl9_2
    | spl9_5 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl9_2
    | spl9_5 ),
    inference(subsumption_resolution,[],[f92,f87])).

fof(f87,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK6(sK2,sK1),X0),k2_zfmisc_1(sK1,X1))
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f79,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f79,plain,
    ( ~ r2_hidden(sK6(sK2,sK1),sK1)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f92,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK1),sK7(sK2,sK1)),k2_zfmisc_1(sK1,sK0))
    | spl9_2
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f68,f85,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK1),sK7(sK2,sK1)),sK2)
    | spl9_2
    | spl9_5 ),
    inference(subsumption_resolution,[],[f84,f79])).

fof(f84,plain,
    ( r2_hidden(k4_tarski(sK6(sK2,sK1),sK7(sK2,sK1)),sK2)
    | r2_hidden(sK6(sK2,sK1),sK1)
    | spl9_2 ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,
    ( ! [X0] :
        ( sK1 != X0
        | r2_hidden(k4_tarski(sK6(sK2,X0),sK7(sK2,X0)),sK2)
        | r2_hidden(sK6(sK2,X0),X0) )
    | spl9_2 ),
    inference(superposition,[],[f71,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f70,f31])).

fof(f70,plain,
    ( sK1 != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl9_2 ),
    inference(superposition,[],[f56,f44])).

fof(f56,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f68,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f31,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f83,plain,
    ( ~ spl9_5
    | spl9_6
    | spl9_2 ),
    inference(avatar_split_clause,[],[f75,f54,f81,f77])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK6(sK2,sK1),X0),sK2)
        | ~ r2_hidden(sK6(sK2,sK1),sK1) )
    | spl9_2 ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,
    ( ! [X2,X1] :
        ( sK1 != X1
        | ~ r2_hidden(k4_tarski(sK6(sK2,X1),X2),sK2)
        | ~ r2_hidden(sK6(sK2,X1),X1) )
    | spl9_2 ),
    inference(superposition,[],[f71,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,
    ( spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f32,f54,f64])).

fof(f32,plain,(
    ! [X5] :
      ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | r2_hidden(k4_tarski(X5,sK4(X5)),sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f33,f54,f59])).

fof(f33,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f34,f54,f51])).

fof(f34,plain,(
    ! [X4] :
      ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:52:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.52  % (5671)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.52  % (5667)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.52  % (5675)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.52  % (5696)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.52  % (5671)Refutation not found, incomplete strategy% (5671)------------------------------
% 0.23/0.52  % (5671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (5672)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.52  % (5671)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (5671)Memory used [KB]: 6140
% 0.23/0.52  % (5671)Time elapsed: 0.108 s
% 0.23/0.52  % (5671)------------------------------
% 0.23/0.52  % (5671)------------------------------
% 0.23/0.52  % (5678)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.52  % (5669)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.53  % (5668)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.53  % (5678)Refutation not found, incomplete strategy% (5678)------------------------------
% 0.23/0.53  % (5678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (5678)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (5678)Memory used [KB]: 10618
% 0.23/0.53  % (5678)Time elapsed: 0.111 s
% 0.23/0.53  % (5678)------------------------------
% 0.23/0.53  % (5678)------------------------------
% 0.23/0.53  % (5676)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.53  % (5689)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.53  % (5685)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.53  % (5695)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.19/0.54  % (5679)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.54  % (5683)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.19/0.54  % (5670)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.19/0.55  % (5693)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.19/0.55  % (5690)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.19/0.55  % (5693)Refutation found. Thanks to Tanya!
% 1.19/0.55  % SZS status Theorem for theBenchmark
% 1.19/0.55  % SZS output start Proof for theBenchmark
% 1.19/0.55  fof(f121,plain,(
% 1.19/0.55    $false),
% 1.19/0.55    inference(avatar_sat_refutation,[],[f57,f62,f66,f83,f95,f106,f120])).
% 1.19/0.55  fof(f120,plain,(
% 1.19/0.55    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 1.19/0.55    inference(avatar_contradiction_clause,[],[f119])).
% 1.19/0.55  fof(f119,plain,(
% 1.19/0.55    $false | (~spl9_1 | ~spl9_2 | ~spl9_3)),
% 1.19/0.55    inference(subsumption_resolution,[],[f118,f61])).
% 1.19/0.55  fof(f61,plain,(
% 1.19/0.55    r2_hidden(sK3,sK1) | ~spl9_3),
% 1.19/0.55    inference(avatar_component_clause,[],[f59])).
% 1.19/0.55  fof(f59,plain,(
% 1.19/0.55    spl9_3 <=> r2_hidden(sK3,sK1)),
% 1.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.19/0.55  fof(f118,plain,(
% 1.19/0.55    ~r2_hidden(sK3,sK1) | (~spl9_1 | ~spl9_2)),
% 1.19/0.55    inference(forward_demodulation,[],[f115,f107])).
% 1.19/0.55  fof(f107,plain,(
% 1.19/0.55    sK1 = k1_relat_1(sK2) | ~spl9_2),
% 1.19/0.55    inference(backward_demodulation,[],[f67,f55])).
% 1.19/0.55  fof(f55,plain,(
% 1.19/0.55    sK1 = k1_relset_1(sK1,sK0,sK2) | ~spl9_2),
% 1.19/0.55    inference(avatar_component_clause,[],[f54])).
% 1.19/0.55  fof(f54,plain,(
% 1.19/0.55    spl9_2 <=> sK1 = k1_relset_1(sK1,sK0,sK2)),
% 1.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.19/0.55  fof(f67,plain,(
% 1.19/0.55    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 1.19/0.55    inference(unit_resulting_resolution,[],[f31,f44])).
% 1.19/0.55  fof(f44,plain,(
% 1.19/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.55    inference(cnf_transformation,[],[f10])).
% 1.19/0.55  fof(f10,plain,(
% 1.19/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.55    inference(ennf_transformation,[],[f5])).
% 1.19/0.55  fof(f5,axiom,(
% 1.19/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.19/0.55  fof(f31,plain,(
% 1.19/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.19/0.55    inference(cnf_transformation,[],[f17])).
% 1.19/0.55  fof(f17,plain,(
% 1.19/0.55    (sK1 != k1_relset_1(sK1,sK0,sK2) | (! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2) & r2_hidden(sK3,sK1))) & (sK1 = k1_relset_1(sK1,sK0,sK2) | ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f16,f15,f14])).
% 1.19/0.55  fof(f14,plain,(
% 1.19/0.55    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((sK1 != k1_relset_1(sK1,sK0,sK2) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK2) & r2_hidden(X3,sK1))) & (sK1 = k1_relset_1(sK1,sK0,sK2) | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.19/0.55    introduced(choice_axiom,[])).
% 1.19/0.55  fof(f15,plain,(
% 1.19/0.55    ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),sK2) & r2_hidden(X3,sK1)) => (! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2) & r2_hidden(sK3,sK1))),
% 1.19/0.55    introduced(choice_axiom,[])).
% 1.19/0.55  fof(f16,plain,(
% 1.19/0.55    ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),sK2) => r2_hidden(k4_tarski(X5,sK4(X5)),sK2))),
% 1.19/0.55    introduced(choice_axiom,[])).
% 1.19/0.55  fof(f13,plain,(
% 1.19/0.55    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.19/0.55    inference(rectify,[],[f12])).
% 1.19/0.55  fof(f12,plain,(
% 1.19/0.55    ? [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.19/0.55    inference(flattening,[],[f11])).
% 1.19/0.55  fof(f11,plain,(
% 1.19/0.55    ? [X0,X1,X2] : (((k1_relset_1(X1,X0,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (k1_relset_1(X1,X0,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.19/0.55    inference(nnf_transformation,[],[f8])).
% 1.19/0.55  fof(f8,plain,(
% 1.19/0.55    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <~> k1_relset_1(X1,X0,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.19/0.55    inference(ennf_transformation,[],[f7])).
% 1.19/0.55  % (5684)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.19/0.55  fof(f7,negated_conjecture,(
% 1.19/0.55    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.19/0.55    inference(negated_conjecture,[],[f6])).
% 1.19/0.55  fof(f6,conjecture,(
% 1.19/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 1.19/0.55  fof(f115,plain,(
% 1.19/0.55    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~spl9_1),
% 1.19/0.55    inference(unit_resulting_resolution,[],[f52,f49])).
% 1.19/0.55  fof(f49,plain,(
% 1.19/0.55    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 1.19/0.55    inference(equality_resolution,[],[f38])).
% 1.19/0.55  fof(f38,plain,(
% 1.19/0.55    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.19/0.55    inference(cnf_transformation,[],[f27])).
% 1.19/0.55  fof(f27,plain,(
% 1.19/0.55    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f23,f26,f25,f24])).
% 1.19/0.55  fof(f24,plain,(
% 1.19/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.19/0.55    introduced(choice_axiom,[])).
% 1.19/0.55  fof(f25,plain,(
% 1.19/0.55    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 1.19/0.55    introduced(choice_axiom,[])).
% 1.19/0.55  fof(f26,plain,(
% 1.19/0.55    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 1.19/0.55    introduced(choice_axiom,[])).
% 1.19/0.55  fof(f23,plain,(
% 1.19/0.55    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.19/0.55    inference(rectify,[],[f22])).
% 1.19/0.55  fof(f22,plain,(
% 1.19/0.55    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.19/0.55    inference(nnf_transformation,[],[f4])).
% 1.19/0.55  fof(f4,axiom,(
% 1.19/0.55    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.19/0.55  fof(f52,plain,(
% 1.19/0.55    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2)) ) | ~spl9_1),
% 1.19/0.55    inference(avatar_component_clause,[],[f51])).
% 1.19/0.55  fof(f51,plain,(
% 1.19/0.55    spl9_1 <=> ! [X4] : ~r2_hidden(k4_tarski(sK3,X4),sK2)),
% 1.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.19/0.55  fof(f106,plain,(
% 1.19/0.55    ~spl9_4 | ~spl9_5 | ~spl9_6),
% 1.19/0.55    inference(avatar_contradiction_clause,[],[f105])).
% 1.19/0.55  fof(f105,plain,(
% 1.19/0.55    $false | (~spl9_4 | ~spl9_5 | ~spl9_6)),
% 1.19/0.55    inference(subsumption_resolution,[],[f101,f82])).
% 1.19/0.55  fof(f82,plain,(
% 1.19/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK6(sK2,sK1),X0),sK2)) ) | ~spl9_6),
% 1.19/0.55    inference(avatar_component_clause,[],[f81])).
% 1.19/0.55  fof(f81,plain,(
% 1.19/0.55    spl9_6 <=> ! [X0] : ~r2_hidden(k4_tarski(sK6(sK2,sK1),X0),sK2)),
% 1.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.19/0.55  fof(f101,plain,(
% 1.19/0.55    r2_hidden(k4_tarski(sK6(sK2,sK1),sK4(sK6(sK2,sK1))),sK2) | (~spl9_4 | ~spl9_5)),
% 1.19/0.55    inference(unit_resulting_resolution,[],[f78,f65])).
% 1.19/0.55  fof(f65,plain,(
% 1.19/0.55    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(k4_tarski(X5,sK4(X5)),sK2)) ) | ~spl9_4),
% 1.19/0.55    inference(avatar_component_clause,[],[f64])).
% 1.19/0.55  fof(f64,plain,(
% 1.19/0.55    spl9_4 <=> ! [X5] : (r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1))),
% 1.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.19/0.55  fof(f78,plain,(
% 1.19/0.55    r2_hidden(sK6(sK2,sK1),sK1) | ~spl9_5),
% 1.19/0.55    inference(avatar_component_clause,[],[f77])).
% 1.19/0.55  fof(f77,plain,(
% 1.19/0.55    spl9_5 <=> r2_hidden(sK6(sK2,sK1),sK1)),
% 1.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.19/0.55  fof(f95,plain,(
% 1.19/0.55    spl9_2 | spl9_5),
% 1.19/0.55    inference(avatar_contradiction_clause,[],[f94])).
% 1.19/0.55  fof(f94,plain,(
% 1.19/0.55    $false | (spl9_2 | spl9_5)),
% 1.19/0.55    inference(subsumption_resolution,[],[f92,f87])).
% 1.19/0.55  fof(f87,plain,(
% 1.19/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK6(sK2,sK1),X0),k2_zfmisc_1(sK1,X1))) ) | spl9_5),
% 1.19/0.55    inference(unit_resulting_resolution,[],[f79,f45])).
% 1.19/0.55  fof(f45,plain,(
% 1.19/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.19/0.55    inference(cnf_transformation,[],[f30])).
% 1.19/0.55  fof(f30,plain,(
% 1.19/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.19/0.55    inference(flattening,[],[f29])).
% 1.19/0.55  fof(f29,plain,(
% 1.19/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.19/0.55    inference(nnf_transformation,[],[f2])).
% 1.19/0.55  fof(f2,axiom,(
% 1.19/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.19/0.55  fof(f79,plain,(
% 1.19/0.55    ~r2_hidden(sK6(sK2,sK1),sK1) | spl9_5),
% 1.19/0.55    inference(avatar_component_clause,[],[f77])).
% 1.19/0.55  fof(f92,plain,(
% 1.19/0.55    r2_hidden(k4_tarski(sK6(sK2,sK1),sK7(sK2,sK1)),k2_zfmisc_1(sK1,sK0)) | (spl9_2 | spl9_5)),
% 1.19/0.55    inference(unit_resulting_resolution,[],[f68,f85,f35])).
% 1.19/0.55  fof(f35,plain,(
% 1.19/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f21])).
% 1.19/0.55  fof(f21,plain,(
% 1.19/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).
% 1.19/0.55  fof(f20,plain,(
% 1.19/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.19/0.55    introduced(choice_axiom,[])).
% 1.19/0.55  fof(f19,plain,(
% 1.19/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.19/0.55    inference(rectify,[],[f18])).
% 1.19/0.55  fof(f18,plain,(
% 1.19/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.19/0.55    inference(nnf_transformation,[],[f9])).
% 1.19/0.55  fof(f9,plain,(
% 1.19/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.19/0.55    inference(ennf_transformation,[],[f1])).
% 1.19/0.55  fof(f1,axiom,(
% 1.19/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.19/0.55  fof(f85,plain,(
% 1.19/0.55    r2_hidden(k4_tarski(sK6(sK2,sK1),sK7(sK2,sK1)),sK2) | (spl9_2 | spl9_5)),
% 1.19/0.55    inference(subsumption_resolution,[],[f84,f79])).
% 1.19/0.55  fof(f84,plain,(
% 1.19/0.55    r2_hidden(k4_tarski(sK6(sK2,sK1),sK7(sK2,sK1)),sK2) | r2_hidden(sK6(sK2,sK1),sK1) | spl9_2),
% 1.19/0.55    inference(equality_resolution,[],[f72])).
% 1.19/0.55  fof(f72,plain,(
% 1.19/0.55    ( ! [X0] : (sK1 != X0 | r2_hidden(k4_tarski(sK6(sK2,X0),sK7(sK2,X0)),sK2) | r2_hidden(sK6(sK2,X0),X0)) ) | spl9_2),
% 1.19/0.55    inference(superposition,[],[f71,f40])).
% 1.19/0.55  fof(f40,plain,(
% 1.19/0.55    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f27])).
% 1.19/0.55  fof(f71,plain,(
% 1.19/0.55    sK1 != k1_relat_1(sK2) | spl9_2),
% 1.19/0.55    inference(subsumption_resolution,[],[f70,f31])).
% 1.19/0.55  fof(f70,plain,(
% 1.19/0.55    sK1 != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl9_2),
% 1.19/0.55    inference(superposition,[],[f56,f44])).
% 1.19/0.55  fof(f56,plain,(
% 1.19/0.55    sK1 != k1_relset_1(sK1,sK0,sK2) | spl9_2),
% 1.19/0.55    inference(avatar_component_clause,[],[f54])).
% 1.19/0.55  fof(f68,plain,(
% 1.19/0.55    r1_tarski(sK2,k2_zfmisc_1(sK1,sK0))),
% 1.19/0.55    inference(unit_resulting_resolution,[],[f31,f42])).
% 1.19/0.55  fof(f42,plain,(
% 1.19/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.19/0.55    inference(cnf_transformation,[],[f28])).
% 1.19/0.55  fof(f28,plain,(
% 1.19/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.19/0.55    inference(nnf_transformation,[],[f3])).
% 1.19/0.55  fof(f3,axiom,(
% 1.19/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.19/0.55  fof(f83,plain,(
% 1.19/0.55    ~spl9_5 | spl9_6 | spl9_2),
% 1.19/0.55    inference(avatar_split_clause,[],[f75,f54,f81,f77])).
% 1.19/0.55  fof(f75,plain,(
% 1.19/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK6(sK2,sK1),X0),sK2) | ~r2_hidden(sK6(sK2,sK1),sK1)) ) | spl9_2),
% 1.19/0.55    inference(equality_resolution,[],[f73])).
% 1.19/0.55  fof(f73,plain,(
% 1.19/0.55    ( ! [X2,X1] : (sK1 != X1 | ~r2_hidden(k4_tarski(sK6(sK2,X1),X2),sK2) | ~r2_hidden(sK6(sK2,X1),X1)) ) | spl9_2),
% 1.19/0.55    inference(superposition,[],[f71,f41])).
% 1.19/0.55  fof(f41,plain,(
% 1.19/0.55    ( ! [X0,X3,X1] : (k1_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f27])).
% 1.19/0.55  fof(f66,plain,(
% 1.19/0.55    spl9_4 | spl9_2),
% 1.19/0.55    inference(avatar_split_clause,[],[f32,f54,f64])).
% 1.19/0.55  fof(f32,plain,(
% 1.19/0.55    ( ! [X5] : (sK1 = k1_relset_1(sK1,sK0,sK2) | r2_hidden(k4_tarski(X5,sK4(X5)),sK2) | ~r2_hidden(X5,sK1)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f17])).
% 1.19/0.55  fof(f62,plain,(
% 1.19/0.55    spl9_3 | ~spl9_2),
% 1.19/0.55    inference(avatar_split_clause,[],[f33,f54,f59])).
% 1.19/0.55  fof(f33,plain,(
% 1.19/0.55    sK1 != k1_relset_1(sK1,sK0,sK2) | r2_hidden(sK3,sK1)),
% 1.19/0.55    inference(cnf_transformation,[],[f17])).
% 1.19/0.55  fof(f57,plain,(
% 1.19/0.55    spl9_1 | ~spl9_2),
% 1.19/0.55    inference(avatar_split_clause,[],[f34,f54,f51])).
% 1.19/0.55  fof(f34,plain,(
% 1.19/0.55    ( ! [X4] : (sK1 != k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 1.19/0.55    inference(cnf_transformation,[],[f17])).
% 1.19/0.55  % SZS output end Proof for theBenchmark
% 1.19/0.55  % (5693)------------------------------
% 1.19/0.55  % (5693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.55  % (5693)Termination reason: Refutation
% 1.19/0.55  
% 1.19/0.55  % (5693)Memory used [KB]: 10746
% 1.19/0.55  % (5693)Time elapsed: 0.132 s
% 1.19/0.55  % (5693)------------------------------
% 1.19/0.55  % (5693)------------------------------
% 1.19/0.55  % (5681)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.19/0.55  % (5666)Success in time 0.173 s
%------------------------------------------------------------------------------
