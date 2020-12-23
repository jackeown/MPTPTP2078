%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:43 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 473 expanded)
%              Number of leaves         :   26 ( 138 expanded)
%              Depth                    :   22
%              Number of atoms          :  535 (1939 expanded)
%              Number of equality atoms :  155 ( 538 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f813,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f161,f165,f422,f683,f809])).

fof(f809,plain,
    ( ~ spl9_1
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f799])).

fof(f799,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(resolution,[],[f731,f270])).

fof(f270,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f109,f269])).

fof(f269,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) ),
    inference(resolution,[],[f106,f110])).

fof(f110,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f65,f108])).

fof(f108,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f69,f107])).

fof(f107,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f80,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f69,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f109,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f67,f108,f108])).

fof(f67,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f731,plain,
    ( ! [X10,X9] : r1_tarski(k9_relat_1(sK3,X9),X10)
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f709,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f709,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(k1_xboole_0,sK6(sK3,sK7(k9_relat_1(sK3,X9),X10)))
        | r1_tarski(k9_relat_1(sK3,X9),X10) )
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f255,f421])).

fof(f421,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl9_7
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f255,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(k1_relat_1(sK3),sK6(sK3,sK7(k9_relat_1(sK3,X9),X10)))
        | r1_tarski(k9_relat_1(sK3,X9),X10) )
    | ~ spl9_1 ),
    inference(resolution,[],[f236,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f236,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK3,sK7(k9_relat_1(sK3,X0),X1)),k1_relat_1(sK3))
        | r1_tarski(k9_relat_1(sK3,X0),X1) )
    | ~ spl9_1 ),
    inference(resolution,[],[f233,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f230,f155])).

fof(f155,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl9_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl9_1 ),
    inference(resolution,[],[f215,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f215,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,k2_relat_1(sK3))
        | ~ r2_hidden(X1,X2)
        | r2_hidden(sK6(sK3,X1),k1_relat_1(sK3)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f213,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f212,f155])).

fof(f212,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f125,f63])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f44,f47,f46,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f683,plain,
    ( ~ spl9_1
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f679])).

fof(f679,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f665,f270])).

fof(f665,plain,
    ( ! [X23,X22] : r1_tarski(k9_relat_1(sK3,X22),k2_enumset1(X23,X23,X23,k1_funct_1(sK3,sK0)))
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f654,f368])).

fof(f368,plain,
    ( ! [X14,X15] :
        ( ~ r1_tarski(k2_relat_1(sK3),X15)
        | r1_tarski(k9_relat_1(sK3,X14),X15) )
    | ~ spl9_1 ),
    inference(duplicate_literal_removal,[],[f366])).

fof(f366,plain,
    ( ! [X14,X15] :
        ( r1_tarski(k9_relat_1(sK3,X14),X15)
        | ~ r1_tarski(k2_relat_1(sK3),X15)
        | r1_tarski(k9_relat_1(sK3,X14),X15) )
    | ~ spl9_1 ),
    inference(resolution,[],[f356,f150])).

fof(f150,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK7(X3,X4),X5)
      | ~ r1_tarski(X5,X4)
      | r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f89,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f356,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK7(k9_relat_1(sK3,X6),X7),k2_relat_1(sK3))
        | r1_tarski(k9_relat_1(sK3,X6),X7) )
    | ~ spl9_1 ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK7(k9_relat_1(sK3,X6),X7),k2_relat_1(sK3))
        | r1_tarski(k9_relat_1(sK3,X6),X7)
        | r1_tarski(k9_relat_1(sK3,X6),X7) )
    | ~ spl9_1 ),
    inference(superposition,[],[f252,f331])).

fof(f331,plain,
    ( ! [X0,X1] :
        ( sK7(k9_relat_1(sK3,X0),X1) = k1_funct_1(sK3,sK6(sK3,sK7(k9_relat_1(sK3,X0),X1)))
        | r1_tarski(k9_relat_1(sK3,X0),X1) )
    | ~ spl9_1 ),
    inference(resolution,[],[f328,f90])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0 )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f325,f155])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl9_1 ),
    inference(resolution,[],[f324,f81])).

fof(f324,plain,
    ( ! [X8,X7] :
        ( ~ r1_tarski(X8,k2_relat_1(sK3))
        | ~ r2_hidden(X7,X8)
        | k1_funct_1(sK3,sK6(sK3,X7)) = X7 )
    | ~ spl9_1 ),
    inference(resolution,[],[f317,f89])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k1_funct_1(sK3,sK6(sK3,X0)) = X0 )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f316,f155])).

fof(f316,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | k1_funct_1(sK3,sK6(sK3,X0)) = X0
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f124,f63])).

fof(f124,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK3,sK6(sK3,sK7(k9_relat_1(sK3,X0),X1))),k2_relat_1(sK3))
        | r1_tarski(k9_relat_1(sK3,X0),X1) )
    | ~ spl9_1 ),
    inference(resolution,[],[f236,f209])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f208,f155])).

fof(f208,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f123,f63])).

fof(f123,plain,(
    ! [X6,X0] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f654,plain,
    ( ! [X2] : r1_tarski(k2_relat_1(sK3),k2_enumset1(X2,X2,X2,k1_funct_1(sK3,sK0)))
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f622,f131])).

fof(f131,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f102,f107])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK8(X0,X1,X2) != X1
              & sK8(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sK8(X0,X1,X2) = X1
            | sK8(X0,X1,X2) = X0
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK8(X0,X1,X2) != X1
            & sK8(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sK8(X0,X1,X2) = X1
          | sK8(X0,X1,X2) = X0
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f622,plain,
    ( ! [X18] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK0),X18)
        | r1_tarski(k2_relat_1(sK3),X18) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f619])).

fof(f619,plain,
    ( ! [X18] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK0),X18)
        | r1_tarski(k2_relat_1(sK3),X18)
        | r1_tarski(k2_relat_1(sK3),X18) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(superposition,[],[f91,f587])).

fof(f587,plain,
    ( ! [X9] :
        ( k1_funct_1(sK3,sK0) = sK7(k2_relat_1(sK3),X9)
        | r1_tarski(k2_relat_1(sK3),X9) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f586])).

fof(f586,plain,
    ( ! [X9] :
        ( k1_funct_1(sK3,sK0) = sK7(k2_relat_1(sK3),X9)
        | r1_tarski(k2_relat_1(sK3),X9)
        | r1_tarski(k2_relat_1(sK3),X9) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(superposition,[],[f323,f455])).

fof(f455,plain,
    ( ! [X0] :
        ( sK0 = sK6(sK3,sK7(k2_relat_1(sK3),X0))
        | r1_tarski(k2_relat_1(sK3),X0) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f443,f214])).

fof(f214,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(sK3,sK7(k2_relat_1(sK3),X0)),k1_relat_1(sK3))
        | r1_tarski(k2_relat_1(sK3),X0) )
    | ~ spl9_1 ),
    inference(resolution,[],[f213,f90])).

fof(f443,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | sK0 = X0 )
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f435])).

fof(f435,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | sK0 = X0
        | sK0 = X0 )
    | ~ spl9_4 ),
    inference(superposition,[],[f134,f175])).

fof(f175,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl9_4
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f134,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f100,f107])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f323,plain,
    ( ! [X6] :
        ( sK7(k2_relat_1(sK3),X6) = k1_funct_1(sK3,sK6(sK3,sK7(k2_relat_1(sK3),X6)))
        | r1_tarski(k2_relat_1(sK3),X6) )
    | ~ spl9_1 ),
    inference(resolution,[],[f317,f90])).

fof(f422,plain,
    ( spl9_4
    | spl9_7
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f415,f158,f419,f173])).

fof(f158,plain,
    ( spl9_2
  <=> r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f415,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f114,f160])).

fof(f160,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f92,f108,f108])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f165,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f163,f79])).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f163,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl9_1 ),
    inference(resolution,[],[f162,f110])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl9_1 ),
    inference(resolution,[],[f156,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f156,plain,
    ( ~ v1_relat_1(sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f154])).

fof(f161,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f152,f158,f154])).

fof(f152,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f151,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f151,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f97,f110])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:40:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (21553)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (21545)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (21536)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (21533)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (21534)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (21530)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (21539)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (21531)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (21535)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (21557)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (21546)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (21550)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (21541)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (21532)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (21548)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (21537)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (21544)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (21542)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (21538)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (21549)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.57  % (21556)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (21559)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (21555)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (21547)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (21554)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (21558)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.58  % (21560)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.58  % (21543)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (21551)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.58  % (21552)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.62/0.60  % (21533)Refutation found. Thanks to Tanya!
% 1.62/0.60  % SZS status Theorem for theBenchmark
% 1.62/0.60  % SZS output start Proof for theBenchmark
% 1.62/0.60  fof(f813,plain,(
% 1.62/0.60    $false),
% 1.62/0.60    inference(avatar_sat_refutation,[],[f161,f165,f422,f683,f809])).
% 1.62/0.60  fof(f809,plain,(
% 1.62/0.60    ~spl9_1 | ~spl9_7),
% 1.62/0.60    inference(avatar_contradiction_clause,[],[f799])).
% 1.62/0.60  fof(f799,plain,(
% 1.62/0.60    $false | (~spl9_1 | ~spl9_7)),
% 1.62/0.60    inference(resolution,[],[f731,f270])).
% 1.62/0.60  fof(f270,plain,(
% 1.62/0.60    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.62/0.60    inference(backward_demodulation,[],[f109,f269])).
% 1.62/0.60  fof(f269,plain,(
% 1.62/0.60    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0)) )),
% 1.62/0.60    inference(resolution,[],[f106,f110])).
% 1.62/0.60  fof(f110,plain,(
% 1.62/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.62/0.60    inference(definition_unfolding,[],[f65,f108])).
% 1.62/0.60  fof(f108,plain,(
% 1.62/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.62/0.60    inference(definition_unfolding,[],[f69,f107])).
% 1.62/0.60  fof(f107,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.62/0.60    inference(definition_unfolding,[],[f80,f96])).
% 1.62/0.60  fof(f96,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f7])).
% 1.62/0.60  fof(f7,axiom,(
% 1.62/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.62/0.60  fof(f80,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f6])).
% 1.62/0.60  fof(f6,axiom,(
% 1.62/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.62/0.60  fof(f69,plain,(
% 1.62/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f5])).
% 1.62/0.60  fof(f5,axiom,(
% 1.62/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.62/0.60  fof(f65,plain,(
% 1.62/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.62/0.60    inference(cnf_transformation,[],[f41])).
% 1.62/0.60  fof(f41,plain,(
% 1.62/0.60    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f40])).
% 1.62/0.60  fof(f40,plain,(
% 1.62/0.60    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f24,plain,(
% 1.62/0.60    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.62/0.60    inference(flattening,[],[f23])).
% 1.62/0.60  fof(f23,plain,(
% 1.62/0.60    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.62/0.60    inference(ennf_transformation,[],[f22])).
% 1.62/0.60  fof(f22,negated_conjecture,(
% 1.62/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.62/0.60    inference(negated_conjecture,[],[f21])).
% 1.62/0.60  fof(f21,conjecture,(
% 1.62/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.62/0.60  fof(f106,plain,(
% 1.62/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f39])).
% 1.62/0.60  fof(f39,plain,(
% 1.62/0.60    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.60    inference(ennf_transformation,[],[f20])).
% 1.62/0.60  fof(f20,axiom,(
% 1.62/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.62/0.60  fof(f109,plain,(
% 1.62/0.60    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.62/0.60    inference(definition_unfolding,[],[f67,f108,f108])).
% 1.62/0.60  fof(f67,plain,(
% 1.62/0.60    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.62/0.60    inference(cnf_transformation,[],[f41])).
% 1.62/0.60  fof(f731,plain,(
% 1.62/0.60    ( ! [X10,X9] : (r1_tarski(k9_relat_1(sK3,X9),X10)) ) | (~spl9_1 | ~spl9_7)),
% 1.62/0.60    inference(subsumption_resolution,[],[f709,f68])).
% 1.62/0.60  fof(f68,plain,(
% 1.62/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f3])).
% 1.62/0.60  fof(f3,axiom,(
% 1.62/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.62/0.60  fof(f709,plain,(
% 1.62/0.60    ( ! [X10,X9] : (~r1_tarski(k1_xboole_0,sK6(sK3,sK7(k9_relat_1(sK3,X9),X10))) | r1_tarski(k9_relat_1(sK3,X9),X10)) ) | (~spl9_1 | ~spl9_7)),
% 1.62/0.60    inference(backward_demodulation,[],[f255,f421])).
% 1.62/0.60  fof(f421,plain,(
% 1.62/0.60    k1_xboole_0 = k1_relat_1(sK3) | ~spl9_7),
% 1.62/0.60    inference(avatar_component_clause,[],[f419])).
% 1.62/0.60  fof(f419,plain,(
% 1.62/0.60    spl9_7 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.62/0.60  fof(f255,plain,(
% 1.62/0.60    ( ! [X10,X9] : (~r1_tarski(k1_relat_1(sK3),sK6(sK3,sK7(k9_relat_1(sK3,X9),X10))) | r1_tarski(k9_relat_1(sK3,X9),X10)) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f236,f95])).
% 1.62/0.60  fof(f95,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f35])).
% 1.62/0.60  fof(f35,plain,(
% 1.62/0.60    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.62/0.60    inference(ennf_transformation,[],[f18])).
% 1.62/0.60  fof(f18,axiom,(
% 1.62/0.60    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.62/0.60  fof(f236,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r2_hidden(sK6(sK3,sK7(k9_relat_1(sK3,X0),X1)),k1_relat_1(sK3)) | r1_tarski(k9_relat_1(sK3,X0),X1)) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f233,f90])).
% 1.62/0.60  fof(f90,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f55])).
% 1.62/0.60  fof(f55,plain,(
% 1.62/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f53,f54])).
% 1.62/0.60  fof(f54,plain,(
% 1.62/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f53,plain,(
% 1.62/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.60    inference(rectify,[],[f52])).
% 1.62/0.60  fof(f52,plain,(
% 1.62/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.60    inference(nnf_transformation,[],[f34])).
% 1.62/0.60  fof(f34,plain,(
% 1.62/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.60    inference(ennf_transformation,[],[f1])).
% 1.62/0.60  fof(f1,axiom,(
% 1.62/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.60  fof(f233,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3))) ) | ~spl9_1),
% 1.62/0.60    inference(subsumption_resolution,[],[f230,f155])).
% 1.62/0.60  fof(f155,plain,(
% 1.62/0.60    v1_relat_1(sK3) | ~spl9_1),
% 1.62/0.60    inference(avatar_component_clause,[],[f154])).
% 1.62/0.60  fof(f154,plain,(
% 1.62/0.60    spl9_1 <=> v1_relat_1(sK3)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.62/0.60  fof(f230,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f215,f81])).
% 1.62/0.60  fof(f81,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f29])).
% 1.62/0.60  fof(f29,plain,(
% 1.62/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.62/0.60    inference(ennf_transformation,[],[f12])).
% 1.62/0.60  fof(f12,axiom,(
% 1.62/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.62/0.60  fof(f215,plain,(
% 1.62/0.60    ( ! [X2,X1] : (~r1_tarski(X2,k2_relat_1(sK3)) | ~r2_hidden(X1,X2) | r2_hidden(sK6(sK3,X1),k1_relat_1(sK3))) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f213,f89])).
% 1.62/0.60  fof(f89,plain,(
% 1.62/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f55])).
% 1.62/0.60  fof(f213,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3))) ) | ~spl9_1),
% 1.62/0.60    inference(subsumption_resolution,[],[f212,f155])).
% 1.62/0.60  fof(f212,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK6(sK3,X0),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 1.62/0.60    inference(resolution,[],[f125,f63])).
% 1.62/0.60  fof(f63,plain,(
% 1.62/0.60    v1_funct_1(sK3)),
% 1.62/0.60    inference(cnf_transformation,[],[f41])).
% 1.62/0.60  fof(f125,plain,(
% 1.62/0.60    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.62/0.60    inference(equality_resolution,[],[f73])).
% 1.62/0.60  fof(f73,plain,(
% 1.62/0.60    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f48])).
% 1.62/0.60  fof(f48,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f44,f47,f46,f45])).
% 1.62/0.60  fof(f45,plain,(
% 1.62/0.60    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f46,plain,(
% 1.62/0.60    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f47,plain,(
% 1.62/0.60    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f44,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.60    inference(rectify,[],[f43])).
% 1.62/0.60  fof(f43,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.60    inference(nnf_transformation,[],[f28])).
% 1.62/0.60  fof(f28,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.60    inference(flattening,[],[f27])).
% 1.62/0.60  fof(f27,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.62/0.60    inference(ennf_transformation,[],[f16])).
% 1.62/0.60  fof(f16,axiom,(
% 1.62/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.62/0.60  fof(f683,plain,(
% 1.62/0.60    ~spl9_1 | ~spl9_4),
% 1.62/0.60    inference(avatar_contradiction_clause,[],[f679])).
% 1.62/0.60  fof(f679,plain,(
% 1.62/0.60    $false | (~spl9_1 | ~spl9_4)),
% 1.62/0.60    inference(resolution,[],[f665,f270])).
% 1.62/0.60  fof(f665,plain,(
% 1.62/0.60    ( ! [X23,X22] : (r1_tarski(k9_relat_1(sK3,X22),k2_enumset1(X23,X23,X23,k1_funct_1(sK3,sK0)))) ) | (~spl9_1 | ~spl9_4)),
% 1.62/0.60    inference(resolution,[],[f654,f368])).
% 1.62/0.60  fof(f368,plain,(
% 1.62/0.60    ( ! [X14,X15] : (~r1_tarski(k2_relat_1(sK3),X15) | r1_tarski(k9_relat_1(sK3,X14),X15)) ) | ~spl9_1),
% 1.62/0.60    inference(duplicate_literal_removal,[],[f366])).
% 1.62/0.60  fof(f366,plain,(
% 1.62/0.60    ( ! [X14,X15] : (r1_tarski(k9_relat_1(sK3,X14),X15) | ~r1_tarski(k2_relat_1(sK3),X15) | r1_tarski(k9_relat_1(sK3,X14),X15)) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f356,f150])).
% 1.62/0.60  fof(f150,plain,(
% 1.62/0.60    ( ! [X4,X5,X3] : (~r2_hidden(sK7(X3,X4),X5) | ~r1_tarski(X5,X4) | r1_tarski(X3,X4)) )),
% 1.62/0.60    inference(resolution,[],[f89,f91])).
% 1.62/0.60  fof(f91,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f55])).
% 1.62/0.60  fof(f356,plain,(
% 1.62/0.60    ( ! [X6,X7] : (r2_hidden(sK7(k9_relat_1(sK3,X6),X7),k2_relat_1(sK3)) | r1_tarski(k9_relat_1(sK3,X6),X7)) ) | ~spl9_1),
% 1.62/0.60    inference(duplicate_literal_removal,[],[f355])).
% 1.62/0.60  fof(f355,plain,(
% 1.62/0.60    ( ! [X6,X7] : (r2_hidden(sK7(k9_relat_1(sK3,X6),X7),k2_relat_1(sK3)) | r1_tarski(k9_relat_1(sK3,X6),X7) | r1_tarski(k9_relat_1(sK3,X6),X7)) ) | ~spl9_1),
% 1.62/0.60    inference(superposition,[],[f252,f331])).
% 1.62/0.60  fof(f331,plain,(
% 1.62/0.60    ( ! [X0,X1] : (sK7(k9_relat_1(sK3,X0),X1) = k1_funct_1(sK3,sK6(sK3,sK7(k9_relat_1(sK3,X0),X1))) | r1_tarski(k9_relat_1(sK3,X0),X1)) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f328,f90])).
% 1.62/0.60  fof(f328,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0) ) | ~spl9_1),
% 1.62/0.60    inference(subsumption_resolution,[],[f325,f155])).
% 1.62/0.60  fof(f325,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f324,f81])).
% 1.62/0.60  fof(f324,plain,(
% 1.62/0.60    ( ! [X8,X7] : (~r1_tarski(X8,k2_relat_1(sK3)) | ~r2_hidden(X7,X8) | k1_funct_1(sK3,sK6(sK3,X7)) = X7) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f317,f89])).
% 1.62/0.60  fof(f317,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0) ) | ~spl9_1),
% 1.62/0.60    inference(subsumption_resolution,[],[f316,f155])).
% 1.62/0.60  fof(f316,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k1_funct_1(sK3,sK6(sK3,X0)) = X0 | ~v1_relat_1(sK3)) )),
% 1.62/0.60    inference(resolution,[],[f124,f63])).
% 1.62/0.60  fof(f124,plain,(
% 1.62/0.60    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK6(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 1.62/0.60    inference(equality_resolution,[],[f74])).
% 1.62/0.60  fof(f74,plain,(
% 1.62/0.60    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f48])).
% 1.62/0.60  fof(f252,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r2_hidden(k1_funct_1(sK3,sK6(sK3,sK7(k9_relat_1(sK3,X0),X1))),k2_relat_1(sK3)) | r1_tarski(k9_relat_1(sK3,X0),X1)) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f236,f209])).
% 1.62/0.60  fof(f209,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl9_1),
% 1.62/0.60    inference(subsumption_resolution,[],[f208,f155])).
% 1.62/0.60  fof(f208,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 1.62/0.60    inference(resolution,[],[f123,f63])).
% 1.62/0.60  fof(f123,plain,(
% 1.62/0.60    ( ! [X6,X0] : (~v1_funct_1(X0) | ~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.62/0.60    inference(equality_resolution,[],[f122])).
% 1.62/0.60  fof(f122,plain,(
% 1.62/0.60    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.60    inference(equality_resolution,[],[f75])).
% 1.62/0.60  fof(f75,plain,(
% 1.62/0.60    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f48])).
% 1.62/0.60  fof(f654,plain,(
% 1.62/0.60    ( ! [X2] : (r1_tarski(k2_relat_1(sK3),k2_enumset1(X2,X2,X2,k1_funct_1(sK3,sK0)))) ) | (~spl9_1 | ~spl9_4)),
% 1.62/0.60    inference(resolution,[],[f622,f131])).
% 1.62/0.60  fof(f131,plain,(
% 1.62/0.60    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 1.62/0.60    inference(equality_resolution,[],[f130])).
% 1.62/0.60  fof(f130,plain,(
% 1.62/0.60    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 1.62/0.60    inference(equality_resolution,[],[f119])).
% 1.62/0.60  fof(f119,plain,(
% 1.62/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.62/0.60    inference(definition_unfolding,[],[f102,f107])).
% 1.62/0.60  fof(f102,plain,(
% 1.62/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.62/0.60    inference(cnf_transformation,[],[f62])).
% 1.62/0.60  fof(f62,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK8(X0,X1,X2) != X1 & sK8(X0,X1,X2) != X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X1 | sK8(X0,X1,X2) = X0 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f60,f61])).
% 1.62/0.60  fof(f61,plain,(
% 1.62/0.60    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X1 & sK8(X0,X1,X2) != X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X1 | sK8(X0,X1,X2) = X0 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f60,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.60    inference(rectify,[],[f59])).
% 1.62/0.60  fof(f59,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.60    inference(flattening,[],[f58])).
% 1.62/0.60  fof(f58,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.60    inference(nnf_transformation,[],[f4])).
% 1.62/0.60  fof(f4,axiom,(
% 1.62/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.62/0.60  fof(f622,plain,(
% 1.62/0.60    ( ! [X18] : (~r2_hidden(k1_funct_1(sK3,sK0),X18) | r1_tarski(k2_relat_1(sK3),X18)) ) | (~spl9_1 | ~spl9_4)),
% 1.62/0.60    inference(duplicate_literal_removal,[],[f619])).
% 1.62/0.60  fof(f619,plain,(
% 1.62/0.60    ( ! [X18] : (~r2_hidden(k1_funct_1(sK3,sK0),X18) | r1_tarski(k2_relat_1(sK3),X18) | r1_tarski(k2_relat_1(sK3),X18)) ) | (~spl9_1 | ~spl9_4)),
% 1.62/0.60    inference(superposition,[],[f91,f587])).
% 1.62/0.60  fof(f587,plain,(
% 1.62/0.60    ( ! [X9] : (k1_funct_1(sK3,sK0) = sK7(k2_relat_1(sK3),X9) | r1_tarski(k2_relat_1(sK3),X9)) ) | (~spl9_1 | ~spl9_4)),
% 1.62/0.60    inference(duplicate_literal_removal,[],[f586])).
% 1.62/0.60  fof(f586,plain,(
% 1.62/0.60    ( ! [X9] : (k1_funct_1(sK3,sK0) = sK7(k2_relat_1(sK3),X9) | r1_tarski(k2_relat_1(sK3),X9) | r1_tarski(k2_relat_1(sK3),X9)) ) | (~spl9_1 | ~spl9_4)),
% 1.62/0.60    inference(superposition,[],[f323,f455])).
% 1.62/0.60  fof(f455,plain,(
% 1.62/0.60    ( ! [X0] : (sK0 = sK6(sK3,sK7(k2_relat_1(sK3),X0)) | r1_tarski(k2_relat_1(sK3),X0)) ) | (~spl9_1 | ~spl9_4)),
% 1.62/0.60    inference(resolution,[],[f443,f214])).
% 1.62/0.60  fof(f214,plain,(
% 1.62/0.60    ( ! [X0] : (r2_hidden(sK6(sK3,sK7(k2_relat_1(sK3),X0)),k1_relat_1(sK3)) | r1_tarski(k2_relat_1(sK3),X0)) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f213,f90])).
% 1.62/0.60  fof(f443,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | sK0 = X0) ) | ~spl9_4),
% 1.62/0.60    inference(duplicate_literal_removal,[],[f435])).
% 1.62/0.60  fof(f435,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | sK0 = X0 | sK0 = X0) ) | ~spl9_4),
% 1.62/0.60    inference(superposition,[],[f134,f175])).
% 1.62/0.60  fof(f175,plain,(
% 1.62/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl9_4),
% 1.62/0.60    inference(avatar_component_clause,[],[f173])).
% 1.62/0.60  fof(f173,plain,(
% 1.62/0.60    spl9_4 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.62/0.60  fof(f134,plain,(
% 1.62/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.62/0.60    inference(equality_resolution,[],[f121])).
% 1.62/0.60  fof(f121,plain,(
% 1.62/0.60    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.62/0.60    inference(definition_unfolding,[],[f100,f107])).
% 1.62/0.60  fof(f100,plain,(
% 1.62/0.60    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.62/0.60    inference(cnf_transformation,[],[f62])).
% 1.62/0.60  fof(f323,plain,(
% 1.62/0.60    ( ! [X6] : (sK7(k2_relat_1(sK3),X6) = k1_funct_1(sK3,sK6(sK3,sK7(k2_relat_1(sK3),X6))) | r1_tarski(k2_relat_1(sK3),X6)) ) | ~spl9_1),
% 1.62/0.60    inference(resolution,[],[f317,f90])).
% 1.62/0.60  fof(f422,plain,(
% 1.62/0.60    spl9_4 | spl9_7 | ~spl9_2),
% 1.62/0.60    inference(avatar_split_clause,[],[f415,f158,f419,f173])).
% 1.62/0.60  fof(f158,plain,(
% 1.62/0.60    spl9_2 <=> r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.62/0.60  fof(f415,plain,(
% 1.62/0.60    k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl9_2),
% 1.62/0.60    inference(resolution,[],[f114,f160])).
% 1.62/0.60  fof(f160,plain,(
% 1.62/0.60    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl9_2),
% 1.62/0.60    inference(avatar_component_clause,[],[f158])).
% 1.62/0.60  fof(f114,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.62/0.60    inference(definition_unfolding,[],[f92,f108,f108])).
% 1.62/0.60  fof(f92,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f57])).
% 1.62/0.60  fof(f57,plain,(
% 1.62/0.60    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.62/0.60    inference(flattening,[],[f56])).
% 1.62/0.60  fof(f56,plain,(
% 1.62/0.60    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.62/0.60    inference(nnf_transformation,[],[f8])).
% 1.62/0.60  fof(f8,axiom,(
% 1.62/0.60    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.62/0.60  fof(f165,plain,(
% 1.62/0.60    spl9_1),
% 1.62/0.60    inference(avatar_contradiction_clause,[],[f164])).
% 1.62/0.60  fof(f164,plain,(
% 1.62/0.60    $false | spl9_1),
% 1.62/0.60    inference(subsumption_resolution,[],[f163,f79])).
% 1.62/0.60  fof(f79,plain,(
% 1.62/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f11])).
% 1.62/0.60  fof(f11,axiom,(
% 1.62/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.62/0.60  fof(f163,plain,(
% 1.62/0.60    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl9_1),
% 1.62/0.60    inference(resolution,[],[f162,f110])).
% 1.62/0.60  fof(f162,plain,(
% 1.62/0.60    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl9_1),
% 1.62/0.60    inference(resolution,[],[f156,f72])).
% 1.62/0.60  fof(f72,plain,(
% 1.62/0.60    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f26])).
% 1.62/0.60  fof(f26,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f9])).
% 1.62/0.60  fof(f9,axiom,(
% 1.62/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.62/0.60  fof(f156,plain,(
% 1.62/0.60    ~v1_relat_1(sK3) | spl9_1),
% 1.62/0.60    inference(avatar_component_clause,[],[f154])).
% 1.62/0.60  fof(f161,plain,(
% 1.62/0.60    ~spl9_1 | spl9_2),
% 1.62/0.60    inference(avatar_split_clause,[],[f152,f158,f154])).
% 1.62/0.60  fof(f152,plain,(
% 1.62/0.60    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 1.62/0.60    inference(resolution,[],[f151,f83])).
% 1.62/0.60  fof(f83,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f49])).
% 1.62/0.60  fof(f49,plain,(
% 1.62/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.62/0.60    inference(nnf_transformation,[],[f31])).
% 1.62/0.60  fof(f31,plain,(
% 1.62/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.62/0.60    inference(ennf_transformation,[],[f10])).
% 1.62/0.60  fof(f10,axiom,(
% 1.62/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.62/0.60  fof(f151,plain,(
% 1.62/0.60    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.62/0.60    inference(resolution,[],[f97,f110])).
% 1.62/0.60  fof(f97,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f36])).
% 1.62/0.60  fof(f36,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.60    inference(ennf_transformation,[],[f19])).
% 1.62/0.60  fof(f19,axiom,(
% 1.62/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.62/0.60  % SZS output end Proof for theBenchmark
% 1.62/0.60  % (21533)------------------------------
% 1.62/0.60  % (21533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (21533)Termination reason: Refutation
% 1.62/0.60  
% 1.62/0.60  % (21533)Memory used [KB]: 11129
% 1.62/0.60  % (21533)Time elapsed: 0.164 s
% 1.62/0.60  % (21533)------------------------------
% 1.62/0.60  % (21533)------------------------------
% 1.62/0.60  % (21528)Success in time 0.237 s
%------------------------------------------------------------------------------
