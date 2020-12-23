%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 208 expanded)
%              Number of leaves         :   21 (  70 expanded)
%              Depth                    :   21
%              Number of atoms          :  386 ( 874 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f154,f236,f240,f476])).

fof(f476,plain,
    ( ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f38,f468,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f468,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f465,f231])).

fof(f231,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl10_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f465,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(resolution,[],[f429,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sQ9_eqProxy(k7_relat_1(X1,X0),X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f44,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f429,plain,
    ( ~ sQ9_eqProxy(k7_relat_1(sK2,sK1),sK2)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(resolution,[],[f428,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sQ9_eqProxy(k2_relat_1(X0),k2_relat_1(X1))
      | ~ sQ9_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f428,plain,
    ( ~ sQ9_eqProxy(k2_relat_1(k7_relat_1(sK2,sK1)),k2_relat_1(sK2))
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f424,f231])).

fof(f424,plain,
    ( ~ sQ9_eqProxy(k2_relat_1(k7_relat_1(sK2,sK1)),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(resolution,[],[f399,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sQ9_eqProxy(k2_relat_1(k7_relat_1(X1,X0)),k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f42,f58])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f399,plain,
    ( ! [X5] :
        ( ~ sQ9_eqProxy(X5,k9_relat_1(sK2,sK1))
        | ~ sQ9_eqProxy(X5,k2_relat_1(sK2)) )
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(resolution,[],[f376,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sQ9_eqProxy(X1,X0)
      | ~ sQ9_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f376,plain,
    ( ! [X1] :
        ( ~ sQ9_eqProxy(k2_relat_1(sK2),X1)
        | ~ sQ9_eqProxy(X1,k9_relat_1(sK2,sK1)) )
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(resolution,[],[f368,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sQ9_eqProxy(X0,X2)
      | ~ sQ9_eqProxy(X1,X2)
      | ~ sQ9_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f368,plain,
    ( ~ sQ9_eqProxy(k2_relat_1(sK2),k9_relat_1(sK2,sK1))
    | ~ spl10_3
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(resolution,[],[f356,f126])).

fof(f126,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl10_3
  <=> r2_hidden(sK3,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f356,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ sQ9_eqProxy(X0,k9_relat_1(sK2,sK1)) )
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(resolution,[],[f258,f82])).

fof(f82,plain,(
    ! [X0] : sQ9_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f258,plain,
    ( ! [X2,X1] :
        ( ~ sQ9_eqProxy(X2,sK3)
        | ~ r2_hidden(X2,X1)
        | ~ sQ9_eqProxy(X1,k9_relat_1(sK2,sK1)) )
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(resolution,[],[f256,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ sQ9_eqProxy(X2,X3)
      | ~ r2_hidden(X0,X2)
      | ~ sQ9_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f256,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f255,f231])).

fof(f255,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl10_8 ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,
    ( ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl10_8 ),
    inference(resolution,[],[f247,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
            & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f247,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK8(sK3,X3,sK2),sK1)
        | ~ r2_hidden(sK3,k9_relat_1(sK2,X3)) )
    | ~ spl10_8 ),
    inference(resolution,[],[f235,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK3,X0,sK2),sK1)
        | ~ r2_hidden(sK3,k9_relat_1(sK2,X0)) )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl10_8
  <=> ! [X0] :
        ( ~ r2_hidden(sK3,k9_relat_1(sK2,X0))
        | ~ m1_subset_1(sK8(sK3,X0,sK2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK4,sK3),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f26,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(X5,sK3),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK4,sK3),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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

fof(f240,plain,(
    spl10_7 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl10_7 ),
    inference(unit_resulting_resolution,[],[f38,f232,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f232,plain,
    ( ~ v1_relat_1(sK2)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f230])).

fof(f236,plain,
    ( ~ spl10_7
    | spl10_8
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f218,f86,f234,f230])).

fof(f86,plain,
    ( spl10_1
  <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k9_relat_1(sK2,X0))
        | ~ v1_relat_1(sK2)
        | ~ m1_subset_1(sK8(sK3,X0,sK2),sK1) )
    | ~ spl10_1 ),
    inference(resolution,[],[f50,f121])).

fof(f121,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f41,f88])).

fof(f88,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f41,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f154,plain,
    ( ~ spl10_1
    | spl10_3 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl10_1
    | spl10_3 ),
    inference(subsumption_resolution,[],[f149,f38])).

fof(f149,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl10_1
    | spl10_3 ),
    inference(resolution,[],[f145,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sQ9_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_proxy_replacement,[],[f54,f58])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f145,plain,
    ( ~ sQ9_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(sK2))
    | ~ spl10_1
    | spl10_3 ),
    inference(resolution,[],[f139,f88])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ sQ9_eqProxy(X0,k2_relat_1(sK2)) )
    | spl10_3 ),
    inference(resolution,[],[f134,f82])).

fof(f134,plain,
    ( ! [X2,X1] :
        ( ~ sQ9_eqProxy(X2,sK3)
        | ~ r2_hidden(X2,X1)
        | ~ sQ9_eqProxy(X1,k2_relat_1(sK2)) )
    | spl10_3 ),
    inference(resolution,[],[f127,f76])).

fof(f127,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f120,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f82,f94,f82,f112,f76])).

fof(f112,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK3),sK2)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f109,f38])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK3),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
    | spl10_1 ),
    inference(resolution,[],[f108,f63])).

fof(f108,plain,
    ( ! [X6,X7] :
        ( ~ sQ9_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(X7))
        | ~ r2_hidden(k4_tarski(X6,sK3),X7) )
    | spl10_1 ),
    inference(resolution,[],[f101,f83])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ sQ9_eqProxy(k2_relat_1(X0),k2_relset_1(sK1,sK0,sK2))
        | ~ r2_hidden(k4_tarski(X1,sK3),X0) )
    | spl10_1 ),
    inference(resolution,[],[f96,f56])).

fof(f56,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ sQ9_eqProxy(X0,k2_relset_1(sK1,sK0,sK2)) )
    | spl10_1 ),
    inference(resolution,[],[f95,f82])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ sQ9_eqProxy(X1,sK3)
        | ~ r2_hidden(X1,X0)
        | ~ sQ9_eqProxy(X0,k2_relset_1(sK1,sK0,sK2)) )
    | spl10_1 ),
    inference(resolution,[],[f76,f87])).

fof(f87,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f94,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f40,f87])).

fof(f40,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:00:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (18344)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (18352)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (18352)Refutation not found, incomplete strategy% (18352)------------------------------
% 0.21/0.47  % (18352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18352)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (18352)Memory used [KB]: 1663
% 0.21/0.47  % (18352)Time elapsed: 0.063 s
% 0.21/0.47  % (18352)------------------------------
% 0.21/0.47  % (18352)------------------------------
% 0.21/0.48  % (18339)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (18349)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (18344)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f477,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f120,f154,f236,f240,f476])).
% 0.21/0.48  fof(f476,plain,(
% 0.21/0.48    ~spl10_3 | ~spl10_7 | ~spl10_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f473])).
% 0.21/0.48  fof(f473,plain,(
% 0.21/0.48    $false | (~spl10_3 | ~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f38,f468,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f468,plain,(
% 0.21/0.48    ~v4_relat_1(sK2,sK1) | (~spl10_3 | ~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f465,f231])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl10_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f230])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    spl10_7 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.48  fof(f465,plain,(
% 0.21/0.48    ~v4_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (~spl10_3 | ~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(resolution,[],[f429,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ9_eqProxy(k7_relat_1(X1,X0),X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f44,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ9_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.48  fof(f429,plain,(
% 0.21/0.48    ~sQ9_eqProxy(k7_relat_1(sK2,sK1),sK2) | (~spl10_3 | ~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(resolution,[],[f428,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ9_eqProxy(k2_relat_1(X0),k2_relat_1(X1)) | ~sQ9_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f58])).
% 0.21/0.48  fof(f428,plain,(
% 0.21/0.48    ~sQ9_eqProxy(k2_relat_1(k7_relat_1(sK2,sK1)),k2_relat_1(sK2)) | (~spl10_3 | ~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f424,f231])).
% 0.21/0.48  fof(f424,plain,(
% 0.21/0.48    ~sQ9_eqProxy(k2_relat_1(k7_relat_1(sK2,sK1)),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl10_3 | ~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(resolution,[],[f399,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ9_eqProxy(k2_relat_1(k7_relat_1(X1,X0)),k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f42,f58])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    ( ! [X5] : (~sQ9_eqProxy(X5,k9_relat_1(sK2,sK1)) | ~sQ9_eqProxy(X5,k2_relat_1(sK2))) ) | (~spl10_3 | ~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(resolution,[],[f376,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ9_eqProxy(X1,X0) | ~sQ9_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f58])).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    ( ! [X1] : (~sQ9_eqProxy(k2_relat_1(sK2),X1) | ~sQ9_eqProxy(X1,k9_relat_1(sK2,sK1))) ) | (~spl10_3 | ~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(resolution,[],[f368,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sQ9_eqProxy(X0,X2) | ~sQ9_eqProxy(X1,X2) | ~sQ9_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f58])).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    ~sQ9_eqProxy(k2_relat_1(sK2),k9_relat_1(sK2,sK1)) | (~spl10_3 | ~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(resolution,[],[f356,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    r2_hidden(sK3,k2_relat_1(sK2)) | ~spl10_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl10_3 <=> r2_hidden(sK3,k2_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK3,X0) | ~sQ9_eqProxy(X0,k9_relat_1(sK2,sK1))) ) | (~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(resolution,[],[f258,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0] : (sQ9_eqProxy(X0,X0)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f58])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~sQ9_eqProxy(X2,sK3) | ~r2_hidden(X2,X1) | ~sQ9_eqProxy(X1,k9_relat_1(sK2,sK1))) ) | (~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(resolution,[],[f256,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~sQ9_eqProxy(X2,X3) | ~r2_hidden(X0,X2) | ~sQ9_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f58])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | (~spl10_7 | ~spl10_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f255,f231])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl10_8),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f253])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl10_8),
% 0.21/0.48    inference(resolution,[],[f247,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f35,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(rectify,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ( ! [X3] : (~r2_hidden(sK8(sK3,X3,sK2),sK1) | ~r2_hidden(sK3,k9_relat_1(sK2,X3))) ) | ~spl10_8),
% 0.21/0.48    inference(resolution,[],[f235,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK8(sK3,X0,sK2),sK1) | ~r2_hidden(sK3,k9_relat_1(sK2,X0))) ) | ~spl10_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f234])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    spl10_8 <=> ! [X0] : (~r2_hidden(sK3,k9_relat_1(sK2,X0)) | ~m1_subset_1(sK8(sK3,X0,sK2),sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ((! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) & ((r2_hidden(k4_tarski(sK4,sK3),sK2) & m1_subset_1(sK4,sK1)) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f26,f25,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X5] : (r2_hidden(k4_tarski(X5,sK3),sK2) & m1_subset_1(X5,sK1)) => (r2_hidden(k4_tarski(sK4,sK3),sK2) & m1_subset_1(sK4,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.48    inference(rectify,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    spl10_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f237])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    $false | spl10_7),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f38,f232,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl10_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f230])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ~spl10_7 | spl10_8 | ~spl10_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f218,f86,f234,f230])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl10_1 <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK3,k9_relat_1(sK2,X0)) | ~v1_relat_1(sK2) | ~m1_subset_1(sK8(sK3,X0,sK2),sK1)) ) | ~spl10_1),
% 0.21/0.48    inference(resolution,[],[f50,f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl10_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f41,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | ~spl10_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~spl10_1 | spl10_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    $false | (~spl10_1 | spl10_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f38])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl10_1 | spl10_3)),
% 0.21/0.48    inference(resolution,[],[f145,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sQ9_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f54,f58])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ~sQ9_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(sK2)) | (~spl10_1 | spl10_3)),
% 0.21/0.48    inference(resolution,[],[f139,f88])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK3,X0) | ~sQ9_eqProxy(X0,k2_relat_1(sK2))) ) | spl10_3),
% 0.21/0.48    inference(resolution,[],[f134,f82])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~sQ9_eqProxy(X2,sK3) | ~r2_hidden(X2,X1) | ~sQ9_eqProxy(X1,k2_relat_1(sK2))) ) | spl10_3),
% 0.21/0.48    inference(resolution,[],[f127,f76])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k2_relat_1(sK2)) | spl10_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f125])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl10_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    $false | spl10_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f82,f94,f82,f112,f76])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK3),sK2)) ) | spl10_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f109,f38])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK3),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) ) | spl10_1),
% 0.21/0.48    inference(resolution,[],[f108,f63])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X6,X7] : (~sQ9_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(X7)) | ~r2_hidden(k4_tarski(X6,sK3),X7)) ) | spl10_1),
% 0.21/0.48    inference(resolution,[],[f101,f83])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sQ9_eqProxy(k2_relat_1(X0),k2_relset_1(sK1,sK0,sK2)) | ~r2_hidden(k4_tarski(X1,sK3),X0)) ) | spl10_1),
% 0.21/0.48    inference(resolution,[],[f96,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f29,f32,f31,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.48    inference(rectify,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK3,X0) | ~sQ9_eqProxy(X0,k2_relset_1(sK1,sK0,sK2))) ) | spl10_1),
% 0.21/0.48    inference(resolution,[],[f95,f82])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sQ9_eqProxy(X1,sK3) | ~r2_hidden(X1,X0) | ~sQ9_eqProxy(X0,k2_relset_1(sK1,sK0,sK2))) ) | spl10_1),
% 0.21/0.48    inference(resolution,[],[f76,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | spl10_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK4,sK3),sK2) | spl10_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f40,f87])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK4,sK3),sK2) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (18344)------------------------------
% 0.21/0.48  % (18344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18344)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (18344)Memory used [KB]: 6268
% 0.21/0.48  % (18344)Time elapsed: 0.061 s
% 0.21/0.48  % (18344)------------------------------
% 0.21/0.48  % (18344)------------------------------
% 0.21/0.48  % (18338)Success in time 0.129 s
%------------------------------------------------------------------------------
