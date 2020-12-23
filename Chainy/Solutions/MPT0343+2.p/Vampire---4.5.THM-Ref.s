%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0343+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 155 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  304 ( 777 expanded)
%              Number of equality atoms :   26 (  84 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2440,f2444,f2458,f2471])).

fof(f2471,plain,
    ( ~ spl69_11
    | spl69_12 ),
    inference(avatar_contradiction_clause,[],[f2468])).

fof(f2468,plain,
    ( $false
    | ~ spl69_11
    | spl69_12 ),
    inference(unit_resulting_resolution,[],[f2439,f2434,f2459,f2300])).

fof(f2300,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,sK4) ) ),
    inference(resolution,[],[f2297,f922])).

fof(f922,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK2)
      | ~ r2_hidden(X3,sK3)
      | r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f717])).

fof(f717,plain,
    ( sK3 != sK4
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK3)
            | ~ r2_hidden(X3,sK4) )
          & ( r2_hidden(X3,sK4)
            | ~ r2_hidden(X3,sK3) ) )
        | ~ m1_subset_1(X3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f714,f716,f715])).

fof(f715,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK3 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK3)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK3) ) )
              | ~ m1_subset_1(X3,sK2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f716,plain,
    ( ? [X2] :
        ( sK3 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK3)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK3) ) )
            | ~ m1_subset_1(X3,sK2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK2)) )
   => ( sK3 != sK4
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK3)
              | ~ r2_hidden(X3,sK4) )
            & ( r2_hidden(X3,sK4)
              | ~ r2_hidden(X3,sK3) ) )
          | ~ m1_subset_1(X3,sK2) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f714,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f479])).

fof(f479,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f478])).

fof(f478,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f464])).

fof(f464,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f463])).

fof(f463,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(f2297,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f1051,f970])).

fof(f970,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f723])).

fof(f723,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f721,f722])).

fof(f722,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f721,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f720])).

fof(f720,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1051,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f744])).

fof(f744,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f493])).

fof(f493,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f451])).

fof(f451,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f2459,plain,
    ( r2_hidden(sK25(sK3,sK4),sK2)
    | ~ spl69_11 ),
    inference(resolution,[],[f2434,f2359])).

fof(f2359,plain,(
    ! [X18] :
      ( ~ r2_hidden(X18,sK3)
      | r2_hidden(X18,sK2) ) ),
    inference(resolution,[],[f1146,f2294])).

fof(f2294,plain,(
    r1_tarski(sK3,sK2) ),
    inference(resolution,[],[f2290,f1624])).

fof(f1624,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f1155])).

fof(f1155,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f788])).

fof(f788,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK34(X0,X1),X0)
            | ~ r2_hidden(sK34(X0,X1),X1) )
          & ( r1_tarski(sK34(X0,X1),X0)
            | r2_hidden(sK34(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK34])],[f786,f787])).

fof(f787,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK34(X0,X1),X0)
          | ~ r2_hidden(sK34(X0,X1),X1) )
        & ( r1_tarski(sK34(X0,X1),X0)
          | r2_hidden(sK34(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f786,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f785])).

fof(f785,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f2290,plain,(
    r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
    inference(subsumption_resolution,[],[f2283,f930])).

fof(f930,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f457])).

fof(f457,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f2283,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f1050,f920])).

fof(f920,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f717])).

fof(f1050,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f744])).

fof(f1146,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f778])).

fof(f778,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK30(X0,X1),X1)
          & r2_hidden(sK30(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK30])],[f776,f777])).

fof(f777,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK30(X0,X1),X1)
        & r2_hidden(sK30(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f776,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f775])).

fof(f775,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f555])).

fof(f555,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2434,plain,
    ( r2_hidden(sK25(sK3,sK4),sK3)
    | ~ spl69_11 ),
    inference(avatar_component_clause,[],[f2433])).

fof(f2433,plain,
    ( spl69_11
  <=> r2_hidden(sK25(sK3,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl69_11])])).

fof(f2439,plain,
    ( ~ r2_hidden(sK25(sK3,sK4),sK4)
    | spl69_12 ),
    inference(avatar_component_clause,[],[f2437])).

fof(f2437,plain,
    ( spl69_12
  <=> r2_hidden(sK25(sK3,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl69_12])])).

fof(f2458,plain,
    ( spl69_11
    | ~ spl69_12 ),
    inference(avatar_contradiction_clause,[],[f2455])).

fof(f2455,plain,
    ( $false
    | spl69_11
    | ~ spl69_12 ),
    inference(unit_resulting_resolution,[],[f2435,f2438,f2445,f2299])).

fof(f2299,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f2297,f923])).

fof(f923,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK2)
      | ~ r2_hidden(X3,sK4)
      | r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f717])).

fof(f2445,plain,
    ( r2_hidden(sK25(sK3,sK4),sK2)
    | ~ spl69_12 ),
    inference(resolution,[],[f2438,f2367])).

fof(f2367,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK4)
      | r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f1091,f921])).

fof(f921,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f717])).

fof(f1091,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f526])).

fof(f526,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f458])).

fof(f458,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f2438,plain,
    ( r2_hidden(sK25(sK3,sK4),sK4)
    | ~ spl69_12 ),
    inference(avatar_component_clause,[],[f2437])).

fof(f2435,plain,
    ( ~ r2_hidden(sK25(sK3,sK4),sK3)
    | spl69_11 ),
    inference(avatar_component_clause,[],[f2433])).

fof(f2444,plain,
    ( spl69_11
    | spl69_12 ),
    inference(avatar_contradiction_clause,[],[f2443])).

fof(f2443,plain,
    ( $false
    | spl69_11
    | spl69_12 ),
    inference(unit_resulting_resolution,[],[f1729,f2435,f2439,f1832])).

fof(f1832,plain,(
    ! [X0,X1] :
      ( sQ68_eqProxy(X0,X1)
      | r2_hidden(sK25(X0,X1),X1)
      | r2_hidden(sK25(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f1124,f1712])).

fof(f1712,plain,(
    ! [X1,X0] :
      ( sQ68_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ68_eqProxy])])).

fof(f1124,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK25(X0,X1),X1)
      | r2_hidden(sK25(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f762])).

fof(f762,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK25(X0,X1),X1)
          | ~ r2_hidden(sK25(X0,X1),X0) )
        & ( r2_hidden(sK25(X0,X1),X1)
          | r2_hidden(sK25(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f760,f761])).

fof(f761,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK25(X0,X1),X1)
          | ~ r2_hidden(sK25(X0,X1),X0) )
        & ( r2_hidden(sK25(X0,X1),X1)
          | r2_hidden(sK25(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f760,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f550])).

fof(f550,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f1729,plain,(
    ~ sQ68_eqProxy(sK3,sK4) ),
    inference(equality_proxy_replacement,[],[f924,f1712])).

fof(f924,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f717])).

fof(f2440,plain,
    ( ~ spl69_11
    | ~ spl69_12 ),
    inference(avatar_split_clause,[],[f2382,f2437,f2433])).

fof(f2382,plain,
    ( ~ r2_hidden(sK25(sK3,sK4),sK4)
    | ~ r2_hidden(sK25(sK3,sK4),sK3) ),
    inference(resolution,[],[f1831,f1729])).

fof(f1831,plain,(
    ! [X0,X1] :
      ( sQ68_eqProxy(X0,X1)
      | ~ r2_hidden(sK25(X0,X1),X1)
      | ~ r2_hidden(sK25(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f1125,f1712])).

fof(f1125,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK25(X0,X1),X1)
      | ~ r2_hidden(sK25(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f762])).
%------------------------------------------------------------------------------
