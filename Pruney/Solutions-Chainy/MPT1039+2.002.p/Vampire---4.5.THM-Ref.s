%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 802 expanded)
%              Number of leaves         :   19 ( 261 expanded)
%              Depth                    :   29
%              Number of atoms          :  645 (7153 expanded)
%              Number of equality atoms :   97 (1243 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f153,f184,f188,f197,f231,f292,f363])).

fof(f363,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(resolution,[],[f354,f312])).

fof(f312,plain,
    ( ! [X0] : ~ sP0(X0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f311,f304])).

fof(f304,plain,
    ( r1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f259,f232])).

fof(f232,plain,
    ( ! [X1] : k1_xboole_0 = X1
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f187,f196])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl8_10
  <=> ! [X0] :
        ( ~ m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

% (20246)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f187,plain,
    ( ! [X1] :
        ( m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X1 )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl8_9
  <=> ! [X1] :
        ( m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f259,plain,
    ( r1_partfun1(k1_xboole_0,sK5)
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f51,f232])).

fof(f51,plain,(
    r1_partfun1(sK4,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ! [X4] :
        ( ~ r1_partfun1(sK5,X4)
        | ~ r1_partfun1(sK4,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_2(X4,sK2,sK3)
        | ~ v1_funct_1(X4) )
    & r1_partfun1(sK4,sK5)
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_partfun1(X3,X4)
                | ~ r1_partfun1(X2,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X4,X0,X1)
                | ~ v1_funct_1(X4) )
            & r1_partfun1(X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(sK4,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
              | ~ v1_funct_2(X4,sK2,sK3)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(sK4,X3)
          & ( k1_xboole_0 = sK2
            | k1_xboole_0 != sK3 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( ~ r1_partfun1(X3,X4)
            | ~ r1_partfun1(sK4,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
            | ~ v1_funct_2(X4,sK2,sK3)
            | ~ v1_funct_1(X4) )
        & r1_partfun1(sK4,X3)
        & ( k1_xboole_0 = sK2
          | k1_xboole_0 != sK3 )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( ~ r1_partfun1(sK5,X4)
          | ~ r1_partfun1(sK4,X4)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          | ~ v1_funct_2(X4,sK2,sK3)
          | ~ v1_funct_1(X4) )
      & r1_partfun1(sK4,sK5)
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ~ ( ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X4,X0,X1)
                      & v1_funct_1(X4) )
                   => ~ ( r1_partfun1(X3,X4)
                        & r1_partfun1(X2,X4) ) )
                & r1_partfun1(X2,X3)
                & ( k1_xboole_0 = X1
                 => k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X4,X0,X1)
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_2)).

fof(f311,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ sP0(X0,k1_xboole_0,k1_xboole_0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f310,f232])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK5,k1_xboole_0)
        | ~ sP0(X0,k1_xboole_0,k1_xboole_0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f309,f232])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK5,sK6(X0,k1_xboole_0,k1_xboole_0))
        | ~ sP0(X0,k1_xboole_0,k1_xboole_0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f308,f304])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ r1_partfun1(sK5,sK6(X0,k1_xboole_0,k1_xboole_0))
        | ~ sP0(X0,k1_xboole_0,k1_xboole_0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f261,f232])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(k1_xboole_0,sK6(X0,k1_xboole_0,k1_xboole_0))
        | ~ r1_partfun1(sK5,sK6(X0,k1_xboole_0,k1_xboole_0))
        | ~ sP0(X0,k1_xboole_0,k1_xboole_0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f183,f232])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK5,sK6(X0,k1_xboole_0,k1_xboole_0))
        | ~ sP0(X0,k1_xboole_0,k1_xboole_0)
        | ~ r1_partfun1(sK4,sK6(X0,k1_xboole_0,k1_xboole_0)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f182,f80])).

fof(f80,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ sP0(X0,k1_xboole_0,k1_xboole_0)
        | ~ r1_partfun1(sK4,sK6(X0,k1_xboole_0,k1_xboole_0))
        | ~ r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f180,f80])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK4,sK6(X0,k1_xboole_0,k1_xboole_0))
        | ~ sP0(X0,sK3,k1_xboole_0)
        | ~ r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f173,f80])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ sP0(X0,sK3,k1_xboole_0)
        | ~ r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0))
        | ~ r1_partfun1(sK4,sK6(X0,sK3,k1_xboole_0)) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f172,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0))
        | ~ r1_partfun1(sK4,sK6(X0,sK3,k1_xboole_0))
        | ~ sP0(X0,sK3,sK2) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f157,f85])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK4,sK6(X0,sK3,k1_xboole_0))
        | ~ r1_partfun1(sK5,sK6(X0,sK3,sK2))
        | ~ sP0(X0,sK3,sK2) )
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f113,f85])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK5,sK6(X0,sK3,sK2))
      | ~ r1_partfun1(sK4,sK6(X0,sK3,sK2))
      | ~ sP0(X0,sK3,sK2) ) ),
    inference(subsumption_resolution,[],[f112,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK6(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_partfun1(X0,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK6(X0,X1,X2),X2,X1)
        & v1_funct_1(sK6(X0,X1,X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_partfun1(X0,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          & v1_funct_2(X3,X2,X1)
          & v1_funct_1(X3) )
     => ( r1_partfun1(X0,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK6(X0,X1,X2),X2,X1)
        & v1_funct_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_partfun1(X0,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          & v1_funct_2(X3,X2,X1)
          & v1_funct_1(X3) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK4,sK6(X0,sK3,sK2))
      | ~ r1_partfun1(sK5,sK6(X0,sK3,sK2))
      | ~ v1_funct_1(sK6(X0,sK3,sK2))
      | ~ sP0(X0,sK3,sK2) ) ),
    inference(subsumption_resolution,[],[f111,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK4,sK6(X0,sK3,sK2))
      | ~ m1_subset_1(sK6(X0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ r1_partfun1(sK5,sK6(X0,sK3,sK2))
      | ~ v1_funct_1(sK6(X0,sK3,sK2))
      | ~ sP0(X0,sK3,sK2) ) ),
    inference(resolution,[],[f52,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK6(X0,X1,X2),X2,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X4] :
      ( ~ v1_funct_2(X4,sK2,sK3)
      | ~ r1_partfun1(sK4,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ r1_partfun1(sK5,X4)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f354,plain,
    ( ! [X0] : sP0(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f352,f279])).

fof(f279,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl8_15
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f352,plain,
    ( ! [X0] :
        ( sP0(k1_xboole_0,X0,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_xboole_0) )
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(resolution,[],[f291,f258])).

fof(f258,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f46,f232])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f291,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_1(X2)
        | sP0(X2,X1,k1_xboole_0)
        | ~ m1_subset_1(X2,k1_xboole_0) )
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f247,f232])).

fof(f247,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | sP0(X2,X1,k1_xboole_0)
        | ~ v1_funct_1(X2) )
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f74,f232])).

fof(f74,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP0(X2,X1,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f23,f29])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ~ r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_2)).

fof(f292,plain,
    ( spl8_15
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f248,f195,f186,f277])).

fof(f248,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_9
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f66,f232])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f231,plain,
    ( spl8_5
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f167,f83,f104])).

fof(f104,plain,
    ( spl8_5
  <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f167,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f155,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f155,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f49,f85])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f197,plain,
    ( ~ spl8_5
    | spl8_10
    | ~ spl8_3
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f193,f83,f79,f92,f195,f104])).

fof(f92,plain,
    ( spl8_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f192,f76])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f191,f85])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | k1_xboole_0 = X0 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f190,f85])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | k1_xboole_0 = X0 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f189,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | k1_xboole_0 = X0 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f177,f80])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | k1_xboole_0 = X0 )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f163,f76])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | k1_xboole_0 = X0 )
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f146,f85])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f145,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( sP1(sK5,sK4,X1,X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f130,f46])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | sP1(sK5,sK4,X1,X0)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f99,f51])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_partfun1(X0,sK5)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | sP1(sK5,X0,X2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f48,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X3,X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP1(X3,X2,X0,X1)
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f28,f31])).

fof(f31,plain,(
    ! [X3,X2,X0,X1] :
      ( ? [X4] :
          ( r1_partfun1(X3,X4)
          & r1_partfun1(X2,X4)
          & v1_partfun1(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X4) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4)
                      & v1_partfun1(X4,X0) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_partfun1)).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f145,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ sP1(sK5,sK4,sK2,X0) ) ),
    inference(resolution,[],[f144,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK7(X0,X1,X2,X3))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
        & r1_partfun1(X1,sK7(X0,X1,X2,X3))
        & v1_partfun1(sK7(X0,X1,X2,X3),X2)
        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(sK7(X0,X1,X2,X3)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_partfun1(X0,X4)
          & r1_partfun1(X1,X4)
          & v1_partfun1(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
          & v1_funct_1(X4) )
     => ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
        & r1_partfun1(X1,sK7(X0,X1,X2,X3))
        & v1_partfun1(sK7(X0,X1,X2,X3),X2)
        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(sK7(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r1_partfun1(X0,X4)
          & r1_partfun1(X1,X4)
          & v1_partfun1(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
          & v1_funct_1(X4) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X3,X2,X0,X1] :
      ( ? [X4] :
          ( r1_partfun1(X3,X4)
          & r1_partfun1(X2,X4)
          & v1_partfun1(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X4) )
      | ~ sP1(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK7(sK5,sK4,sK2,X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f143,f131])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(sK7(sK5,sK4,sK2,X0))
      | ~ sP1(sK5,sK4,sK2,X0) ) ),
    inference(resolution,[],[f142,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X1,sK7(X0,X1,X2,X3))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f142,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK4,sK7(sK5,sK4,sK2,X0))
      | ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(sK7(sK5,sK4,sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f141,f131])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | k1_xboole_0 = X0
      | ~ r1_partfun1(sK4,sK7(sK5,sK4,sK2,X0))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(sK7(sK5,sK4,sK2,X0))
      | ~ sP1(sK5,sK4,sK2,X0) ) ),
    inference(resolution,[],[f140,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK5,sK7(sK5,sK4,sK2,X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | k1_xboole_0 = X0
      | ~ r1_partfun1(sK4,sK7(sK5,sK4,sK2,X0))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(sK7(sK5,sK4,sK2,X0)) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | k1_xboole_0 = X0
      | ~ r1_partfun1(sK4,sK7(sK5,sK4,sK2,X0))
      | ~ m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ r1_partfun1(sK5,sK7(sK5,sK4,sK2,X0))
      | ~ v1_funct_1(sK7(sK5,sK4,sK2,X0)) ) ),
    inference(resolution,[],[f138,f52])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK7(sK5,sK4,X0,X1),X0,X2)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK7(sK5,sK4,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f137,f131])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(sK7(sK5,sK4,X0,X1),X0,X2)
      | ~ m1_subset_1(sK7(sK5,sK4,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ sP1(sK5,sK4,X0,X1) ) ),
    inference(resolution,[],[f134,f67])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK7(sK5,sK4,X1,X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_funct_2(sK7(sK5,sK4,X1,X0),X1,X2)
      | ~ m1_subset_1(sK7(sK5,sK4,X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f133,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_funct_2)).

fof(f133,plain,(
    ! [X2,X3] :
      ( v1_partfun1(sK7(sK5,sK4,X2,X3),X2)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f131,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | v1_partfun1(sK7(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f188,plain,
    ( ~ spl8_5
    | ~ spl8_3
    | spl8_9 ),
    inference(avatar_split_clause,[],[f136,f186,f92,f104])).

fof(f136,plain,(
    ! [X1] :
      ( m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f132,f76])).

fof(f132,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(sK5,sK4,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f131,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f184,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f164,f83,f92])).

fof(f164,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f154,f76])).

fof(f154,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f47,f85])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f153,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f150,f79])).

fof(f150,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f149,f49])).

fof(f149,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f148,f47])).

fof(f148,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(resolution,[],[f146,f132])).

fof(f86,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f50,f83,f79])).

fof(f50,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:23:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (20259)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (20268)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (20261)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (20248)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (20252)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (20249)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (20257)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (20256)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (20264)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (20267)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (20253)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (20250)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (20251)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (20245)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (20252)Refutation not found, incomplete strategy% (20252)------------------------------
% 0.21/0.52  % (20252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20266)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (20252)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20252)Memory used [KB]: 1791
% 0.21/0.52  % (20252)Time elapsed: 0.067 s
% 0.21/0.52  % (20252)------------------------------
% 0.21/0.52  % (20252)------------------------------
% 0.21/0.52  % (20269)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (20251)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f86,f153,f184,f188,f197,f231,f292,f363])).
% 0.21/0.52  fof(f363,plain,(
% 0.21/0.52    ~spl8_1 | ~spl8_2 | ~spl8_9 | ~spl8_10 | ~spl8_15),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f355])).
% 0.21/0.52  fof(f355,plain,(
% 0.21/0.52    $false | (~spl8_1 | ~spl8_2 | ~spl8_9 | ~spl8_10 | ~spl8_15)),
% 0.21/0.52    inference(resolution,[],[f354,f312])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    ( ! [X0] : (~sP0(X0,k1_xboole_0,k1_xboole_0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f311,f304])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    r1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f259,f232])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = X1) ) | (~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f187,f196])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl8_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f195])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    spl8_10 <=> ! [X0] : (~m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.52  % (20246)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X1) ) | ~spl8_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    spl8_9 <=> ! [X1] : (m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    r1_partfun1(k1_xboole_0,sK5) | (~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f51,f232])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    r1_partfun1(sK4,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    (! [X4] : (~r1_partfun1(sK5,X4) | ~r1_partfun1(sK4,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(X4,sK2,sK3) | ~v1_funct_1(X4)) & r1_partfun1(sK4,sK5) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f34,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4)) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(sK4,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(X4,sK2,sK3) | ~v1_funct_1(X4)) & r1_partfun1(sK4,X3) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(sK4,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(X4,sK2,sK3) | ~v1_funct_1(X4)) & r1_partfun1(sK4,X3) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(X3)) => (! [X4] : (~r1_partfun1(sK5,X4) | ~r1_partfun1(sK4,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(X4,sK2,sK3) | ~v1_funct_1(X4)) & r1_partfun1(sK4,sK5) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK5))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4)) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : ((! [X4] : ((~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f18])).
% 0.21/0.52  fof(f18,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_2)).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(k1_xboole_0,k1_xboole_0) | ~sP0(X0,k1_xboole_0,k1_xboole_0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f310,f232])).
% 0.21/0.52  fof(f310,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK5,k1_xboole_0) | ~sP0(X0,k1_xboole_0,k1_xboole_0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f309,f232])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK5,sK6(X0,k1_xboole_0,k1_xboole_0)) | ~sP0(X0,k1_xboole_0,k1_xboole_0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f308,f304])).
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(k1_xboole_0,k1_xboole_0) | ~r1_partfun1(sK5,sK6(X0,k1_xboole_0,k1_xboole_0)) | ~sP0(X0,k1_xboole_0,k1_xboole_0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f261,f232])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(k1_xboole_0,sK6(X0,k1_xboole_0,k1_xboole_0)) | ~r1_partfun1(sK5,sK6(X0,k1_xboole_0,k1_xboole_0)) | ~sP0(X0,k1_xboole_0,k1_xboole_0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f183,f232])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK5,sK6(X0,k1_xboole_0,k1_xboole_0)) | ~sP0(X0,k1_xboole_0,k1_xboole_0) | ~r1_partfun1(sK4,sK6(X0,k1_xboole_0,k1_xboole_0))) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.52    inference(forward_demodulation,[],[f182,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | ~spl8_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl8_1 <=> k1_xboole_0 = sK3),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ( ! [X0] : (~sP0(X0,k1_xboole_0,k1_xboole_0) | ~r1_partfun1(sK4,sK6(X0,k1_xboole_0,k1_xboole_0)) | ~r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0))) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.52    inference(forward_demodulation,[],[f180,f80])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK4,sK6(X0,k1_xboole_0,k1_xboole_0)) | ~sP0(X0,sK3,k1_xboole_0) | ~r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0))) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.52    inference(backward_demodulation,[],[f173,f80])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ( ! [X0] : (~sP0(X0,sK3,k1_xboole_0) | ~r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0)) | ~r1_partfun1(sK4,sK6(X0,sK3,k1_xboole_0))) ) | ~spl8_2),
% 0.21/0.52    inference(forward_demodulation,[],[f172,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl8_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl8_2 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK5,sK6(X0,sK3,k1_xboole_0)) | ~r1_partfun1(sK4,sK6(X0,sK3,k1_xboole_0)) | ~sP0(X0,sK3,sK2)) ) | ~spl8_2),
% 0.21/0.52    inference(forward_demodulation,[],[f157,f85])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK4,sK6(X0,sK3,k1_xboole_0)) | ~r1_partfun1(sK5,sK6(X0,sK3,sK2)) | ~sP0(X0,sK3,sK2)) ) | ~spl8_2),
% 0.21/0.52    inference(backward_demodulation,[],[f113,f85])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK5,sK6(X0,sK3,sK2)) | ~r1_partfun1(sK4,sK6(X0,sK3,sK2)) | ~sP0(X0,sK3,sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f112,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_1(sK6(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_partfun1(X0,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6(X0,X1,X2),X2,X1) & v1_funct_1(sK6(X0,X1,X2))) | ~sP0(X0,X1,X2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (r1_partfun1(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X3,X2,X1) & v1_funct_1(X3)) => (r1_partfun1(X0,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6(X0,X1,X2),X2,X1) & v1_funct_1(sK6(X0,X1,X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (? [X3] : (r1_partfun1(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X3,X2,X1) & v1_funct_1(X3)) | ~sP0(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~sP0(X2,X1,X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~sP0(X2,X1,X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK4,sK6(X0,sK3,sK2)) | ~r1_partfun1(sK5,sK6(X0,sK3,sK2)) | ~v1_funct_1(sK6(X0,sK3,sK2)) | ~sP0(X0,sK3,sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f111,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK4,sK6(X0,sK3,sK2)) | ~m1_subset_1(sK6(X0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~r1_partfun1(sK5,sK6(X0,sK3,sK2)) | ~v1_funct_1(sK6(X0,sK3,sK2)) | ~sP0(X0,sK3,sK2)) )),
% 0.21/0.52    inference(resolution,[],[f52,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(sK6(X0,X1,X2),X2,X1) | ~sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X4] : (~v1_funct_2(X4,sK2,sK3) | ~r1_partfun1(sK4,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~r1_partfun1(sK5,X4) | ~v1_funct_1(X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(k1_xboole_0,X0,k1_xboole_0)) ) | (~spl8_9 | ~spl8_10 | ~spl8_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f352,f279])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_xboole_0) | ~spl8_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f277])).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    spl8_15 <=> m1_subset_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(k1_xboole_0,X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_xboole_0)) ) | (~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(resolution,[],[f291,f258])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    v1_funct_1(k1_xboole_0) | (~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f46,f232])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    v1_funct_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~v1_funct_1(X2) | sP0(X2,X1,k1_xboole_0) | ~m1_subset_1(X2,k1_xboole_0)) ) | (~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f247,f232])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | sP0(X2,X1,k1_xboole_0) | ~v1_funct_1(X2)) ) | (~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f74,f232])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X1] : (sP0(X2,X1,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (sP0(X2,X1,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(definition_folding,[],[f23,f29])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (? [X3] : (r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((? [X3] : (r1_partfun1(X2,X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~r1_partfun1(X2,X3)) & (k1_xboole_0 = X1 => k1_xboole_0 = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_2)).
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    spl8_15 | ~spl8_9 | ~spl8_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f248,f195,f186,f277])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    m1_subset_1(k1_xboole_0,k1_xboole_0) | (~spl8_9 | ~spl8_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f66,f232])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    spl8_5 | ~spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f167,f83,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl8_5 <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~spl8_2),
% 0.21/0.52    inference(forward_demodulation,[],[f155,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) | ~spl8_2),
% 0.21/0.52    inference(backward_demodulation,[],[f49,f85])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    ~spl8_5 | spl8_10 | ~spl8_3 | ~spl8_1 | ~spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f193,f83,f79,f92,f195,f104])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl8_3 <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.52    inference(forward_demodulation,[],[f192,f76])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.52    inference(forward_demodulation,[],[f191,f85])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_xboole_0 = X0) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.52    inference(forward_demodulation,[],[f190,f85])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_xboole_0 = X0) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.52    inference(forward_demodulation,[],[f189,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | ~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_xboole_0 = X0) ) | (~spl8_1 | ~spl8_2)),
% 0.21/0.52    inference(forward_demodulation,[],[f177,f80])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_xboole_0 = X0) ) | ~spl8_2),
% 0.21/0.52    inference(forward_demodulation,[],[f163,f76])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_xboole_0 = X0) ) | ~spl8_2),
% 0.21/0.52    inference(backward_demodulation,[],[f146,f85])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f145,f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP1(sK5,sK4,X1,X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f130,f46])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | sP1(sK5,sK4,X1,X0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(sK4)) )),
% 0.21/0.52    inference(resolution,[],[f99,f51])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_partfun1(X0,sK5) | k1_xboole_0 = X1 | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | sP1(sK5,X0,X2,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f48,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~r1_partfun1(X2,X3) | k1_xboole_0 = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X3,X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (sP1(X3,X2,X0,X1) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(definition_folding,[],[f28,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X3,X2,X0,X1] : (? [X4] : (r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) | ~sP1(X3,X2,X0,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (? [X4] : (r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : ((? [X4] : ((r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4))) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_partfun1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    v1_funct_1(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~sP1(sK5,sK4,sK2,X0)) )),
% 0.21/0.52    inference(resolution,[],[f144,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v1_funct_1(sK7(X0,X1,X2,X3)) | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r1_partfun1(X0,sK7(X0,X1,X2,X3)) & r1_partfun1(X1,sK7(X0,X1,X2,X3)) & v1_partfun1(sK7(X0,X1,X2,X3),X2) & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(sK7(X0,X1,X2,X3))) | ~sP1(X0,X1,X2,X3))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X3,X2,X1,X0] : (? [X4] : (r1_partfun1(X0,X4) & r1_partfun1(X1,X4) & v1_partfun1(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X4)) => (r1_partfun1(X0,sK7(X0,X1,X2,X3)) & r1_partfun1(X1,sK7(X0,X1,X2,X3)) & v1_partfun1(sK7(X0,X1,X2,X3),X2) & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(sK7(X0,X1,X2,X3))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (? [X4] : (r1_partfun1(X0,X4) & r1_partfun1(X1,X4) & v1_partfun1(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X4)) | ~sP1(X0,X1,X2,X3))),
% 0.21/0.52    inference(rectify,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X3,X2,X0,X1] : (? [X4] : (r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) | ~sP1(X3,X2,X0,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f31])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_1(sK7(sK5,sK4,sK2,X0)) | k1_xboole_0 = X0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f143,f131])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | k1_xboole_0 = X0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(sK7(sK5,sK4,sK2,X0)) | ~sP1(sK5,sK4,sK2,X0)) )),
% 0.21/0.52    inference(resolution,[],[f142,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r1_partfun1(X1,sK7(X0,X1,X2,X3)) | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK4,sK7(sK5,sK4,sK2,X0)) | ~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | k1_xboole_0 = X0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(sK7(sK5,sK4,sK2,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f141,f131])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | k1_xboole_0 = X0 | ~r1_partfun1(sK4,sK7(sK5,sK4,sK2,X0)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(sK7(sK5,sK4,sK2,X0)) | ~sP1(sK5,sK4,sK2,X0)) )),
% 0.21/0.52    inference(resolution,[],[f140,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r1_partfun1(X0,sK7(X0,X1,X2,X3)) | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_partfun1(sK5,sK7(sK5,sK4,sK2,X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | k1_xboole_0 = X0 | ~r1_partfun1(sK4,sK7(sK5,sK4,sK2,X0)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(sK7(sK5,sK4,sK2,X0))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | k1_xboole_0 = X0 | ~r1_partfun1(sK4,sK7(sK5,sK4,sK2,X0)) | ~m1_subset_1(sK7(sK5,sK4,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~r1_partfun1(sK5,sK7(sK5,sK4,sK2,X0)) | ~v1_funct_1(sK7(sK5,sK4,sK2,X0))) )),
% 0.21/0.52    inference(resolution,[],[f138,f52])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(sK7(sK5,sK4,X0,X1),X0,X2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK7(sK5,sK4,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f137,f131])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(sK7(sK5,sK4,X0,X1),X0,X2) | ~m1_subset_1(sK7(sK5,sK4,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~sP1(sK5,sK4,X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f134,f67])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(sK7(sK5,sK4,X1,X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_funct_2(sK7(sK5,sK4,X1,X0),X1,X2) | ~m1_subset_1(sK7(sK5,sK4,X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f133,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_funct_2)).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ( ! [X2,X3] : (v1_partfun1(sK7(sK5,sK4,X2,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.52    inference(resolution,[],[f131,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | v1_partfun1(sK7(X0,X1,X2,X3),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    ~spl8_5 | ~spl8_3 | spl8_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f136,f186,f92,f104])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(sK7(sK5,sK4,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X1 | ~m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.52    inference(superposition,[],[f132,f76])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(sK7(sK5,sK4,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(resolution,[],[f131,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    spl8_3 | ~spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f164,f83,f92])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | ~spl8_2),
% 0.21/0.52    inference(forward_demodulation,[],[f154,f76])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3))) | ~spl8_2),
% 0.21/0.52    inference(backward_demodulation,[],[f47,f85])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl8_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f150,f79])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    k1_xboole_0 = sK3),
% 0.21/0.52    inference(subsumption_resolution,[],[f149,f49])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | k1_xboole_0 = sK3),
% 0.21/0.52    inference(subsumption_resolution,[],[f148,f47])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | k1_xboole_0 = sK3),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f147])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.52    inference(resolution,[],[f146,f132])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ~spl8_1 | spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f50,f83,f79])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (20251)------------------------------
% 0.21/0.52  % (20251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20251)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (20251)Memory used [KB]: 10746
% 0.21/0.52  % (20251)Time elapsed: 0.111 s
% 0.21/0.52  % (20251)------------------------------
% 0.21/0.52  % (20251)------------------------------
% 0.21/0.52  % (20263)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (20242)Success in time 0.16 s
%------------------------------------------------------------------------------
