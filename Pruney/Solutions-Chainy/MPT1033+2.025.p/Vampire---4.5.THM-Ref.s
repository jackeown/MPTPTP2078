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
% DateTime   : Thu Dec  3 13:06:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 407 expanded)
%              Number of leaves         :   23 ( 135 expanded)
%              Depth                    :   17
%              Number of atoms          :  458 (2891 expanded)
%              Number of equality atoms :   56 ( 527 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f402,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f203,f258,f259,f276,f281,f296,f302,f342,f345,f401])).

fof(f401,plain,
    ( ~ spl6_4
    | spl6_8
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | ~ spl6_4
    | spl6_8
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f399,f220])).

fof(f220,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl6_15
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f399,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ spl6_4
    | spl6_8
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f398,f155])).

fof(f155,plain,
    ( sK2 != sK3
    | spl6_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_8
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f398,plain,
    ( sK2 = sK3
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f397,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f397,plain,
    ( ~ v1_funct_1(sK2)
    | sK2 = sK3
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f395,f41])).

fof(f41,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f395,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | sK2 = sK3
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(resolution,[],[f373,f303])).

fof(f303,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f37,f89])).

fof(f89,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_4
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f373,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK2))
        | ~ r1_partfun1(X1,sK3)
        | ~ v1_funct_1(X1)
        | sK3 = X1
        | ~ v1_partfun1(X1,sK0) )
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f228,f89])).

fof(f228,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK3)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK3 = X1
        | ~ v1_partfun1(X1,sK0) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl6_17
  <=> ! [X1] :
        ( ~ r1_partfun1(X1,sK3)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK3 = X1
        | ~ v1_partfun1(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f345,plain,
    ( ~ spl6_20
    | spl6_23 ),
    inference(avatar_split_clause,[],[f284,f261,f240])).

fof(f240,plain,
    ( spl6_20
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f261,plain,
    ( spl6_23
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f284,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_23 ),
    inference(resolution,[],[f263,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f263,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f261])).

fof(f342,plain,
    ( ~ spl6_4
    | ~ spl6_6
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6
    | spl6_8 ),
    inference(subsumption_resolution,[],[f340,f155])).

fof(f340,plain,
    ( sK2 = sK3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f98,f89])).

fof(f98,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK3
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_6
  <=> k2_zfmisc_1(sK0,sK1) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f302,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f301,f83,f87])).

fof(f83,plain,
    ( spl6_3
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f301,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f299,f72])).

fof(f72,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f299,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(resolution,[],[f84,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f84,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f296,plain,
    ( spl6_17
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f295,f210,f206,f227])).

fof(f206,plain,
    ( spl6_12
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f210,plain,
    ( spl6_13
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f295,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK3)
        | ~ v1_partfun1(X1,sK0)
        | sK3 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1) )
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f294,f207])).

fof(f207,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f206])).

fof(f294,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK3)
        | ~ v1_partfun1(X1,sK0)
        | sK3 = X1
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1) )
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f287,f211])).

fof(f211,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f210])).

fof(f287,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK3)
      | ~ v1_partfun1(sK3,sK0)
      | ~ v1_partfun1(X1,sK0)
      | sK3 = X1
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f40,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

% (13407)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f281,plain,
    ( ~ spl6_23
    | spl6_6 ),
    inference(avatar_split_clause,[],[f278,f96,f261])).

fof(f278,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK3
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f73,f79])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f51,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f53,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f73,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f55,f40])).

fof(f276,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f38,f206])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f259,plain,
    ( spl6_20
    | spl6_15 ),
    inference(avatar_split_clause,[],[f126,f219,f240])).

fof(f126,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f125,f35])).

fof(f125,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f122,f36])).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f122,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f47,f37])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f258,plain,
    ( spl6_20
    | spl6_13 ),
    inference(avatar_split_clause,[],[f129,f210,f240])).

fof(f129,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f128,f38])).

fof(f128,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f123,f39])).

% (13426)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f39,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f123,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f47,f40])).

fof(f203,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f193,f111])).

fof(f111,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f61,f37])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f193,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f43,f156])).

fof(f156,plain,
    ( sK2 = sK3
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f43,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f181,plain,
    ( spl6_8
    | spl6_3 ),
    inference(avatar_split_clause,[],[f180,f83,f154])).

fof(f180,plain,
    ( sK2 = sK3
    | spl6_3 ),
    inference(subsumption_resolution,[],[f179,f35])).

fof(f179,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK2)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f178,f41])).

fof(f178,plain,
    ( sK2 = sK3
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f175,f127])).

fof(f127,plain,
    ( v1_partfun1(sK2,sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f126,f105])).

fof(f105,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(resolution,[],[f104,f48])).

fof(f104,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl6_3 ),
    inference(resolution,[],[f85,f75])).

fof(f85,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f175,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | sK2 = sK3
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | spl6_3 ),
    inference(resolution,[],[f143,f37])).

fof(f143,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_partfun1(X1,sK0)
        | sK3 = X1
        | ~ r1_partfun1(X1,sK3)
        | ~ v1_funct_1(X1) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f142,f38])).

fof(f142,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK3)
        | ~ v1_partfun1(X1,sK0)
        | sK3 = X1
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f138,f130])).

fof(f130,plain,
    ( v1_partfun1(sK3,sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f129,f105])).

fof(f138,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK3)
      | ~ v1_partfun1(sK3,sK0)
      | ~ v1_partfun1(X1,sK0)
      | sK3 = X1
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f57,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:08:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (13431)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (13423)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.51  % (13416)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (13431)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (13419)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (13404)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (13405)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (13409)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (13406)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (13412)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (13422)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (13430)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (13415)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (13429)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f402,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f181,f203,f258,f259,f276,f281,f296,f302,f342,f345,f401])).
% 0.22/0.53  fof(f401,plain,(
% 0.22/0.53    ~spl6_4 | spl6_8 | ~spl6_15 | ~spl6_17),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f400])).
% 0.22/0.53  fof(f400,plain,(
% 0.22/0.53    $false | (~spl6_4 | spl6_8 | ~spl6_15 | ~spl6_17)),
% 0.22/0.53    inference(subsumption_resolution,[],[f399,f220])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    v1_partfun1(sK2,sK0) | ~spl6_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f219])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    spl6_15 <=> v1_partfun1(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.53  fof(f399,plain,(
% 0.22/0.53    ~v1_partfun1(sK2,sK0) | (~spl6_4 | spl6_8 | ~spl6_17)),
% 0.22/0.53    inference(subsumption_resolution,[],[f398,f155])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    sK2 != sK3 | spl6_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f154])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    spl6_8 <=> sK2 = sK3),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.53  fof(f398,plain,(
% 0.22/0.53    sK2 = sK3 | ~v1_partfun1(sK2,sK0) | (~spl6_4 | ~spl6_17)),
% 0.22/0.53    inference(subsumption_resolution,[],[f397,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    v1_funct_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f22,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 0.22/0.54  fof(f397,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | sK2 = sK3 | ~v1_partfun1(sK2,sK0) | (~spl6_4 | ~spl6_17)),
% 0.22/0.54    inference(subsumption_resolution,[],[f395,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    r1_partfun1(sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f395,plain,(
% 0.22/0.54    ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | sK2 = sK3 | ~v1_partfun1(sK2,sK0) | (~spl6_4 | ~spl6_17)),
% 0.22/0.54    inference(resolution,[],[f373,f303])).
% 0.22/0.54  fof(f303,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK2)) | ~spl6_4),
% 0.22/0.54    inference(backward_demodulation,[],[f37,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl6_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    spl6_4 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f373,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK2)) | ~r1_partfun1(X1,sK3) | ~v1_funct_1(X1) | sK3 = X1 | ~v1_partfun1(X1,sK0)) ) | (~spl6_4 | ~spl6_17)),
% 0.22/0.54    inference(forward_demodulation,[],[f228,f89])).
% 0.22/0.54  fof(f228,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK3 = X1 | ~v1_partfun1(X1,sK0)) ) | ~spl6_17),
% 0.22/0.54    inference(avatar_component_clause,[],[f227])).
% 0.22/0.54  fof(f227,plain,(
% 0.22/0.54    spl6_17 <=> ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK3 = X1 | ~v1_partfun1(X1,sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.54  fof(f345,plain,(
% 0.22/0.54    ~spl6_20 | spl6_23),
% 0.22/0.54    inference(avatar_split_clause,[],[f284,f261,f240])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    spl6_20 <=> v1_xboole_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    spl6_23 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.54  fof(f284,plain,(
% 0.22/0.54    ~v1_xboole_0(sK1) | spl6_23),
% 0.22/0.54    inference(resolution,[],[f263,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl6_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f261])).
% 0.22/0.54  fof(f342,plain,(
% 0.22/0.54    ~spl6_4 | ~spl6_6 | spl6_8),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f341])).
% 0.22/0.54  fof(f341,plain,(
% 0.22/0.54    $false | (~spl6_4 | ~spl6_6 | spl6_8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f340,f155])).
% 0.22/0.54  fof(f340,plain,(
% 0.22/0.54    sK2 = sK3 | (~spl6_4 | ~spl6_6)),
% 0.22/0.54    inference(forward_demodulation,[],[f98,f89])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    k2_zfmisc_1(sK0,sK1) = sK3 | ~spl6_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    spl6_6 <=> k2_zfmisc_1(sK0,sK1) = sK3),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.54  fof(f302,plain,(
% 0.22/0.54    spl6_4 | ~spl6_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f301,f83,f87])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    spl6_3 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.54  fof(f301,plain,(
% 0.22/0.54    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f299,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.54    inference(resolution,[],[f55,f37])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f299,plain,(
% 0.22/0.54    sK2 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl6_3),
% 0.22/0.54    inference(resolution,[],[f84,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | ~spl6_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f83])).
% 0.22/0.54  fof(f296,plain,(
% 0.22/0.54    spl6_17 | ~spl6_12 | ~spl6_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f295,f210,f206,f227])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    spl6_12 <=> v1_funct_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    spl6_13 <=> v1_partfun1(sK3,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.54  fof(f295,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1)) ) | (~spl6_12 | ~spl6_13)),
% 0.22/0.54    inference(subsumption_resolution,[],[f294,f207])).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    v1_funct_1(sK3) | ~spl6_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f206])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1)) ) | ~spl6_13),
% 0.22/0.54    inference(subsumption_resolution,[],[f287,f211])).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    v1_partfun1(sK3,sK0) | ~spl6_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f210])).
% 0.22/0.54  fof(f287,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1)) )),
% 0.22/0.54    inference(resolution,[],[f40,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  % (13407)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f281,plain,(
% 0.22/0.54    ~spl6_23 | spl6_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f278,f96,f261])).
% 0.22/0.54  fof(f278,plain,(
% 0.22/0.54    k2_zfmisc_1(sK0,sK1) = sK3 | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.54    inference(resolution,[],[f73,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~v1_xboole_0(X2)) )),
% 0.22/0.54    inference(resolution,[],[f51,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f53,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(rectify,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.54    inference(resolution,[],[f55,f40])).
% 0.22/0.54  fof(f276,plain,(
% 0.22/0.54    spl6_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f38,f206])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    v1_funct_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    spl6_20 | spl6_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f126,f219,f240])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f125,f35])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f122,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(resolution,[],[f47,f37])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.54  fof(f258,plain,(
% 0.22/0.54    spl6_20 | spl6_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f129,f210,f240])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f128,f38])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ~v1_funct_1(sK3) | v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f123,f39])).
% 0.22/0.54  % (13426)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(resolution,[],[f47,f40])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    ~spl6_8),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f202])).
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    $false | ~spl6_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f193,f111])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.22/0.54    inference(resolution,[],[f61,f37])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.54    inference(condensation,[],[f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl6_8),
% 0.22/0.54    inference(backward_demodulation,[],[f43,f156])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    sK2 = sK3 | ~spl6_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f154])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    spl6_8 | spl6_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f180,f83,f154])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    sK2 = sK3 | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f179,f35])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    sK2 = sK3 | ~v1_funct_1(sK2) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f178,f41])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    sK2 = sK3 | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f175,f127])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    v1_partfun1(sK2,sK0) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f126,f105])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ~v1_xboole_0(sK1) | spl6_3),
% 0.22/0.54    inference(resolution,[],[f104,f48])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl6_3),
% 0.22/0.54    inference(resolution,[],[f85,f75])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl6_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f83])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    ~v1_partfun1(sK2,sK0) | sK2 = sK3 | ~r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | spl6_3),
% 0.22/0.54    inference(resolution,[],[f143,f37])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~r1_partfun1(X1,sK3) | ~v1_funct_1(X1)) ) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f142,f38])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1)) ) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f138,f130])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    v1_partfun1(sK3,sK0) | spl6_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f129,f105])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1)) )),
% 0.22/0.54    inference(resolution,[],[f57,f40])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (13431)------------------------------
% 0.22/0.54  % (13431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13431)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (13431)Memory used [KB]: 6396
% 0.22/0.54  % (13431)Time elapsed: 0.106 s
% 0.22/0.54  % (13431)------------------------------
% 0.22/0.54  % (13431)------------------------------
% 0.22/0.54  % (13408)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (13418)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (13403)Success in time 0.174 s
%------------------------------------------------------------------------------
