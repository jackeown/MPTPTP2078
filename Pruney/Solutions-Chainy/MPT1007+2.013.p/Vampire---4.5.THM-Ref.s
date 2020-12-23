%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 499 expanded)
%              Number of leaves         :   26 ( 142 expanded)
%              Depth                    :   23
%              Number of atoms          :  345 (1573 expanded)
%              Number of equality atoms :   70 ( 404 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f464,plain,(
    $false ),
    inference(subsumption_resolution,[],[f463,f229])).

fof(f229,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f228,f110])).

fof(f110,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f88,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f228,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f225,f105])).

fof(f105,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f69,f62])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f225,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f224,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X2,X1,X0)
          & sP0(X0,X2,X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f27,f41,f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> r2_hidden(k4_tarski(X1,X2),X0) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> k1_xboole_0 = X2 )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f224,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,k1_funct_1(k1_xboole_0,X0),X0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f221,f63])).

fof(f63,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f221,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,k1_funct_1(k1_xboole_0,X0),X0)
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f136,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k4_tarski(X0,k1_funct_1(X1,X0)))
      | ~ sP0(X1,k1_funct_1(X1,X0),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f102,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f102,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,k1_funct_1(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,k1_funct_1(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),X0)
      | k1_funct_1(X0,X2) != X1
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_funct_1(X0,X2) = X1
          | ~ r2_hidden(k4_tarski(X2,X1),X0) )
        & ( r2_hidden(k4_tarski(X2,X1),X0)
          | k1_funct_1(X0,X2) != X1 ) )
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X2,X1] :
      ( ( ( k1_funct_1(X0,X1) = X2
          | ~ r2_hidden(k4_tarski(X1,X2),X0) )
        & ( r2_hidden(k4_tarski(X1,X2),X0)
          | k1_funct_1(X0,X1) != X2 ) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f463,plain,(
    r2_hidden(sK7(k2_enumset1(sK3,sK3,sK3,sK3)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f462,f63])).

fof(f462,plain,(
    r2_hidden(sK7(k2_enumset1(sK3,sK3,sK3,sK3)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f461,f110])).

fof(f461,plain,
    ( r2_hidden(sK7(k2_enumset1(sK3,sK3,sK3,sK3)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f460,f105])).

fof(f460,plain,
    ( r2_hidden(sK7(k2_enumset1(sK3,sK3,sK3,sK3)),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f458,f429])).

fof(f429,plain,(
    ~ r2_hidden(k1_xboole_0,sK4) ),
    inference(subsumption_resolution,[],[f428,f229])).

fof(f428,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,sK4) ),
    inference(forward_demodulation,[],[f414,f63])).

fof(f414,plain,
    ( r2_hidden(sK3,k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f170,f389])).

fof(f389,plain,(
    k1_xboole_0 = sK5 ),
    inference(resolution,[],[f386,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( sP2(sK6(X0),X0)
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP2(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP2(sK6(X0),X0)
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP2(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f28,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f386,plain,(
    ! [X0] : ~ r2_hidden(X0,sK5) ),
    inference(subsumption_resolution,[],[f385,f61])).

fof(f61,plain,(
    ~ r2_hidden(k1_funct_1(sK5,sK3),sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
    & v1_funct_2(sK5,k1_tarski(sK3),sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK5,sK3),sK4)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))
      & v1_funct_2(sK5,k1_tarski(sK3),sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f385,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK5,sK3),sK4)
      | ~ r2_hidden(X0,sK5) ) ),
    inference(duplicate_literal_removal,[],[f381])).

fof(f381,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK5,sK3),sK4)
      | ~ r2_hidden(X0,sK5)
      | ~ r2_hidden(X0,sK5) ) ),
    inference(superposition,[],[f290,f172])).

fof(f172,plain,(
    ! [X0] :
      ( k1_mcart_1(X0) = sK3
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f122,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f89,f94])).

fof(f94,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f68,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f81,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f81,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f122,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
      | ~ r2_hidden(X4,sK5) ) ),
    inference(resolution,[],[f83,f95])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4))) ),
    inference(definition_unfolding,[],[f59,f94])).

fof(f59,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f290,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK5,k1_mcart_1(X0)),sK4)
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f174,f156])).

fof(f156,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(k1_funct_1(sK5,X6),sK4) ) ),
    inference(subsumption_resolution,[],[f155,f57])).

fof(f57,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f155,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(k1_funct_1(sK5,X6),sK4)
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f154,f96])).

fof(f96,plain,(
    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f58,f94])).

fof(f58,plain,(
    v1_funct_2(sK5,k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f154,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(k1_funct_1(sK5,X6),sK4)
      | ~ v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)
      | ~ v1_funct_1(sK5) ) ),
    inference(subsumption_resolution,[],[f152,f60])).

fof(f60,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f46])).

fof(f152,plain,(
    ! [X6] :
      ( k1_xboole_0 = sK4
      | ~ r2_hidden(X6,k2_enumset1(sK3,sK3,sK3,sK3))
      | r2_hidden(k1_funct_1(sK5,X6),sK4)
      | ~ v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f92,f95])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f174,plain,(
    ! [X2] :
      ( r2_hidden(k1_mcart_1(X2),k2_enumset1(sK3,sK3,sK3,sK3))
      | ~ r2_hidden(X2,sK5) ) ),
    inference(resolution,[],[f122,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f170,plain,
    ( r2_hidden(sK3,k1_relat_1(sK5))
    | ~ r2_hidden(k1_xboole_0,sK4) ),
    inference(subsumption_resolution,[],[f169,f118])).

fof(f118,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f95,f88])).

fof(f169,plain,
    ( r2_hidden(sK3,k1_relat_1(sK5))
    | ~ r2_hidden(k1_xboole_0,sK4)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f168,f57])).

fof(f168,plain,
    ( r2_hidden(sK3,k1_relat_1(sK5))
    | ~ r2_hidden(k1_xboole_0,sK4)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f132,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f132,plain,
    ( ~ sP1(k1_xboole_0,sK3,sK5)
    | r2_hidden(sK3,k1_relat_1(sK5))
    | ~ r2_hidden(k1_xboole_0,sK4) ),
    inference(superposition,[],[f61,f100])).

fof(f100,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_funct_1(X2,X1)
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X1) = X0
      | k1_xboole_0 != X0
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_funct_1(X2,X1) = X0
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | k1_funct_1(X2,X1) != X0 ) )
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ( ( k1_funct_1(X0,X1) = X2
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | k1_funct_1(X0,X1) != X2 ) )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP1(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f458,plain,
    ( r2_hidden(k1_xboole_0,sK4)
    | r2_hidden(sK7(k2_enumset1(sK3,sK3,sK3,sK3)),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f420,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f101,f75])).

fof(f101,plain,(
    ! [X2,X1] :
      ( ~ sP1(k1_funct_1(X2,X1),X1,X2)
      | r2_hidden(X1,k1_relat_1(X2))
      | k1_xboole_0 = k1_funct_1(X2,X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_funct_1(X2,X1) != X0
      | r2_hidden(X1,k1_relat_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f420,plain,(
    r2_hidden(k1_funct_1(k1_xboole_0,sK7(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) ),
    inference(backward_demodulation,[],[f182,f389])).

fof(f182,plain,(
    r2_hidden(k1_funct_1(sK5,sK7(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) ),
    inference(subsumption_resolution,[],[f179,f97])).

fof(f97,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f65,f94])).

fof(f65,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f179,plain,
    ( r2_hidden(k1_funct_1(sK5,sK7(k2_enumset1(sK3,sK3,sK3,sK3))),sK4)
    | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f156,f109])).

fof(f109,plain,(
    ! [X1] :
      ( r2_hidden(sK7(X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f82,f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f7,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:36:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (19478)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (19492)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (19477)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19502)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (19475)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (19476)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (19494)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (19484)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (19481)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (19485)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (19487)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (19496)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (19488)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (19486)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (19479)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (19480)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (19482)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (19501)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (19473)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (19474)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (19502)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f464,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f463,f229])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f228,f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    v1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f88,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f225,f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    v1_funct_1(k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f69,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f224,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (sP1(X2,X1,X0) & sP0(X0,X2,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(definition_folding,[],[f27,f41,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X2,X1] : ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP0(X0,X2,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X2,X1,X0] : ((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0)) | ~sP1(X2,X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    ( ! [X0] : (~sP0(k1_xboole_0,k1_funct_1(k1_xboole_0,X0),X0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f221,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    ( ! [X0] : (~sP0(k1_xboole_0,k1_funct_1(k1_xboole_0,X0),X0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 0.21/0.54    inference(resolution,[],[f136,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,k4_tarski(X0,k1_funct_1(X1,X0))) | ~sP0(X1,k1_funct_1(X1,X0),X0) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 0.21/0.54    inference(resolution,[],[f102,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,k1_funct_1(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP0(X0,k1_funct_1(X0,X2),X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),X0) | k1_funct_1(X0,X2) != X1 | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((k1_funct_1(X0,X2) = X1 | ~r2_hidden(k4_tarski(X2,X1),X0)) & (r2_hidden(k4_tarski(X2,X1),X0) | k1_funct_1(X0,X2) != X1)) | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP0(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X0,X2,X1] : (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP0(X0,X2,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f40])).
% 0.21/0.54  fof(f463,plain,(
% 0.21/0.54    r2_hidden(sK7(k2_enumset1(sK3,sK3,sK3,sK3)),k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f462,f63])).
% 0.21/0.54  fof(f462,plain,(
% 0.21/0.54    r2_hidden(sK7(k2_enumset1(sK3,sK3,sK3,sK3)),k1_relat_1(k1_xboole_0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f461,f110])).
% 0.21/0.54  fof(f461,plain,(
% 0.21/0.54    r2_hidden(sK7(k2_enumset1(sK3,sK3,sK3,sK3)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f460,f105])).
% 0.21/0.54  fof(f460,plain,(
% 0.21/0.54    r2_hidden(sK7(k2_enumset1(sK3,sK3,sK3,sK3)),k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f458,f429])).
% 0.21/0.54  fof(f429,plain,(
% 0.21/0.54    ~r2_hidden(k1_xboole_0,sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f428,f229])).
% 0.21/0.54  fof(f428,plain,(
% 0.21/0.54    r2_hidden(sK3,k1_xboole_0) | ~r2_hidden(k1_xboole_0,sK4)),
% 0.21/0.54    inference(forward_demodulation,[],[f414,f63])).
% 0.21/0.54  fof(f414,plain,(
% 0.21/0.54    r2_hidden(sK3,k1_relat_1(k1_xboole_0)) | ~r2_hidden(k1_xboole_0,sK4)),
% 0.21/0.54    inference(backward_demodulation,[],[f170,f389])).
% 0.21/0.54  fof(f389,plain,(
% 0.21/0.54    k1_xboole_0 = sK5),
% 0.21/0.54    inference(resolution,[],[f386,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ! [X0] : ((sP2(sK6(X0),X0) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (sP2(X1,X0) & r2_hidden(X1,X0)) => (sP2(sK6(X0),X0) & r2_hidden(sK6(X0),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (sP2(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(definition_folding,[],[f28,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP2(X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.54  fof(f386,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f385,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ~r2_hidden(k1_funct_1(sK5,sK3),sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ~r2_hidden(k1_funct_1(sK5,sK3),sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK5,sK3),sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4))) & v1_funct_2(sK5,k1_tarski(sK3),sK4) & v1_funct_1(sK5))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f21])).
% 0.21/0.54  fof(f21,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK5,sK3),sK4) | ~r2_hidden(X0,sK5)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f381])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK5,sK3),sK4) | ~r2_hidden(X0,sK5) | ~r2_hidden(X0,sK5)) )),
% 0.21/0.54    inference(superposition,[],[f290,f172])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ( ! [X0] : (k1_mcart_1(X0) = sK3 | ~r2_hidden(X0,sK5)) )),
% 0.21/0.54    inference(resolution,[],[f122,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f89,f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f68,f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f81,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X4] : (r2_hidden(X4,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) | ~r2_hidden(X4,sK5)) )),
% 0.21/0.54    inference(resolution,[],[f83,f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK3),sK4)))),
% 0.21/0.54    inference(definition_unfolding,[],[f59,f94])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK3),sK4)))),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.54  fof(f290,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK5,k1_mcart_1(X0)),sK4) | ~r2_hidden(X0,sK5)) )),
% 0.21/0.54    inference(resolution,[],[f174,f156])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X6] : (~r2_hidden(X6,k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(k1_funct_1(sK5,X6),sK4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f155,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v1_funct_1(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X6] : (~r2_hidden(X6,k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(k1_funct_1(sK5,X6),sK4) | ~v1_funct_1(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f154,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 0.21/0.54    inference(definition_unfolding,[],[f58,f94])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    v1_funct_2(sK5,k1_tarski(sK3),sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X6] : (~r2_hidden(X6,k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(k1_funct_1(sK5,X6),sK4) | ~v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) | ~v1_funct_1(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f152,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    k1_xboole_0 != sK4),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X6] : (k1_xboole_0 = sK4 | ~r2_hidden(X6,k2_enumset1(sK3,sK3,sK3,sK3)) | r2_hidden(k1_funct_1(sK5,X6),sK4) | ~v1_funct_2(sK5,k2_enumset1(sK3,sK3,sK3,sK3),sK4) | ~v1_funct_1(sK5)) )),
% 0.21/0.54    inference(resolution,[],[f92,f95])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(k1_mcart_1(X2),k2_enumset1(sK3,sK3,sK3,sK3)) | ~r2_hidden(X2,sK5)) )),
% 0.21/0.54    inference(resolution,[],[f122,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    r2_hidden(sK3,k1_relat_1(sK5)) | ~r2_hidden(k1_xboole_0,sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f169,f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    v1_relat_1(sK5)),
% 0.21/0.54    inference(resolution,[],[f95,f88])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    r2_hidden(sK3,k1_relat_1(sK5)) | ~r2_hidden(k1_xboole_0,sK4) | ~v1_relat_1(sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f168,f57])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    r2_hidden(sK3,k1_relat_1(sK5)) | ~r2_hidden(k1_xboole_0,sK4) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)),
% 0.21/0.54    inference(resolution,[],[f132,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ~sP1(k1_xboole_0,sK3,sK5) | r2_hidden(sK3,k1_relat_1(sK5)) | ~r2_hidden(k1_xboole_0,sK4)),
% 0.21/0.54    inference(superposition,[],[f61,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k1_xboole_0 = k1_funct_1(X2,X1) | r2_hidden(X1,k1_relat_1(X2)) | ~sP1(k1_xboole_0,X1,X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_funct_1(X2,X1) = X0 | k1_xboole_0 != X0 | r2_hidden(X1,k1_relat_1(X2)) | ~sP1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((k1_funct_1(X2,X1) = X0 | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | k1_funct_1(X2,X1) != X0)) | r2_hidden(X1,k1_relat_1(X2)) | ~sP1(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0)) | ~sP1(X2,X1,X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f41])).
% 0.21/0.54  fof(f458,plain,(
% 0.21/0.54    r2_hidden(k1_xboole_0,sK4) | r2_hidden(sK7(k2_enumset1(sK3,sK3,sK3,sK3)),k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f420,f134])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(resolution,[],[f101,f75])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~sP1(k1_funct_1(X2,X1),X1,X2) | r2_hidden(X1,k1_relat_1(X2)) | k1_xboole_0 = k1_funct_1(X2,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_funct_1(X2,X1) != X0 | r2_hidden(X1,k1_relat_1(X2)) | ~sP1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f48])).
% 0.21/0.54  fof(f420,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(k1_xboole_0,sK7(k2_enumset1(sK3,sK3,sK3,sK3))),sK4)),
% 0.21/0.54    inference(backward_demodulation,[],[f182,f389])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK5,sK7(k2_enumset1(sK3,sK3,sK3,sK3))),sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f179,f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f65,f94])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK5,sK7(k2_enumset1(sK3,sK3,sK3,sK3))),sK4) | v1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.21/0.54    inference(resolution,[],[f156,f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK7(X1),X1) | v1_xboole_0(X1)) )),
% 0.21/0.54    inference(resolution,[],[f82,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK7(X0),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ! [X0] : m1_subset_1(sK7(X0),X0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f7,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK7(X0),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (19502)------------------------------
% 0.21/0.54  % (19502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19502)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (19502)Memory used [KB]: 2046
% 0.21/0.54  % (19502)Time elapsed: 0.141 s
% 0.21/0.54  % (19502)------------------------------
% 0.21/0.54  % (19502)------------------------------
% 0.21/0.54  % (19467)Success in time 0.179 s
%------------------------------------------------------------------------------
