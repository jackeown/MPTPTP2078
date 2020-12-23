%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:44 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 421 expanded)
%              Number of leaves         :   41 ( 145 expanded)
%              Depth                    :   14
%              Number of atoms          :  588 (1857 expanded)
%              Number of equality atoms :   77 ( 189 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f803,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f276,f279,f359,f361,f363,f366,f369,f439,f451,f453,f518,f595,f667,f694,f728,f745,f749,f750,f751,f802])).

fof(f802,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f801])).

fof(f801,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(resolution,[],[f800,f167])).

fof(f167,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f90,f134])).

fof(f134,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f130,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f130,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k6_partfun1(k1_xboole_0) = X1 ) ),
    inference(resolution,[],[f121,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f118,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

% (6064)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f118,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f116,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f83,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f121,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k6_partfun1(k1_xboole_0))
      | k6_partfun1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f119,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,(
    ! [X0] : r1_tarski(k6_partfun1(k1_xboole_0),X0) ),
    inference(resolution,[],[f117,f71])).

fof(f117,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f116,f111])).

fof(f111,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f64,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f90,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f60])).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f800,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f103,f794])).

fof(f794,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f793,f96])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f793,plain,
    ( sK2 = k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f200,f420])).

fof(f420,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl5_19
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f200,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl5_3
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f103,plain,
    ( ~ v2_funct_1(sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f751,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f538,f202,f198])).

fof(f202,plain,
    ( spl5_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f538,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f53,f115])).

fof(f115,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ r1_tarski(X3,X4)
      | X3 = X4 ) ),
    inference(resolution,[],[f69,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f750,plain,
    ( ~ spl5_12
    | ~ spl5_17
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_15
    | spl5_1
    | spl5_19
    | ~ spl5_20
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f585,f273,f422,f418,f101,f356,f414,f352,f348,f410,f344])).

fof(f344,plain,
    ( spl5_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f410,plain,
    ( spl5_17
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f348,plain,
    ( spl5_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f352,plain,
    ( spl5_14
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f414,plain,
    ( spl5_18
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f356,plain,
    ( spl5_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f422,plain,
    ( spl5_20
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f273,plain,
    ( spl5_9
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f585,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_9 ),
    inference(superposition,[],[f84,f275])).

fof(f275,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f273])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f749,plain,(
    spl5_31 ),
    inference(avatar_contradiction_clause,[],[f746])).

fof(f746,plain,
    ( $false
    | spl5_31 ),
    inference(resolution,[],[f740,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f740,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl5_31 ),
    inference(resolution,[],[f727,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f727,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f725])).

fof(f725,plain,
    ( spl5_31
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f745,plain,(
    spl5_30 ),
    inference(avatar_contradiction_clause,[],[f741])).

fof(f741,plain,
    ( $false
    | spl5_30 ),
    inference(resolution,[],[f739,f56])).

fof(f739,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_30 ),
    inference(resolution,[],[f723,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f723,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f721])).

fof(f721,plain,
    ( spl5_30
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f728,plain,
    ( ~ spl5_30
    | ~ spl5_31
    | spl5_2
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f719,f610,f105,f725,f721])).

fof(f105,plain,
    ( spl5_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f610,plain,
    ( spl5_27
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f719,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_27 ),
    inference(superposition,[],[f92,f611])).

fof(f611,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f610])).

fof(f92,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f694,plain,
    ( ~ spl5_15
    | spl5_27
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f692,f588,f610,f356])).

fof(f588,plain,
    ( spl5_23
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f692,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_23 ),
    inference(superposition,[],[f79,f590])).

fof(f590,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f588])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f667,plain,
    ( ~ spl5_9
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f665])).

fof(f665,plain,
    ( $false
    | ~ spl5_9
    | spl5_24 ),
    inference(resolution,[],[f594,f370])).

fof(f370,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f57,f275])).

fof(f57,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f594,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl5_24
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f595,plain,
    ( ~ spl5_14
    | ~ spl5_18
    | ~ spl5_15
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_13
    | spl5_23
    | ~ spl5_24
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f586,f273,f592,f588,f348,f410,f344,f356,f414,f352])).

fof(f586,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_9 ),
    inference(superposition,[],[f82,f275])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f518,plain,
    ( spl5_4
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | spl5_4
    | ~ spl5_19 ),
    inference(resolution,[],[f488,f142])).

fof(f142,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f119,f134])).

fof(f488,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_4
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f460,f96])).

fof(f460,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK2)
    | spl5_4
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f204,f420])).

fof(f204,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f202])).

fof(f453,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | spl5_18 ),
    inference(resolution,[],[f416,f55])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f416,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f414])).

fof(f451,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | spl5_17 ),
    inference(resolution,[],[f412,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f412,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f410])).

fof(f439,plain,(
    spl5_20 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | spl5_20 ),
    inference(resolution,[],[f424,f90])).

fof(f424,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f422])).

fof(f369,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | spl5_15 ),
    inference(resolution,[],[f358,f56])).

fof(f358,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f356])).

fof(f366,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl5_13 ),
    inference(resolution,[],[f350,f53])).

fof(f350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f348])).

fof(f363,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f354,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f354,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f352])).

fof(f361,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | spl5_12 ),
    inference(resolution,[],[f346,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f346,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f344])).

fof(f359,plain,
    ( ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_7 ),
    inference(avatar_split_clause,[],[f341,f265,f356,f352,f348,f344])).

fof(f265,plain,
    ( spl5_7
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f341,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_7 ),
    inference(resolution,[],[f267,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f267,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f265])).

fof(f279,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f271,f64])).

fof(f271,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl5_8
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f276,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f261,f273,f269,f265])).

fof(f261,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f86,f57])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f108,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f58,f105,f101])).

fof(f58,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (6036)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (6043)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (6040)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (6049)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (6038)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (6062)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (6058)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (6054)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (6039)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (6050)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (6037)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (6041)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (6044)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (6051)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (6042)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (6056)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (6061)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (6060)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (6065)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (6063)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (6058)Refutation not found, incomplete strategy% (6058)------------------------------
% 0.20/0.54  % (6058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6058)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6058)Memory used [KB]: 10874
% 0.20/0.54  % (6058)Time elapsed: 0.085 s
% 0.20/0.54  % (6058)------------------------------
% 0.20/0.54  % (6058)------------------------------
% 0.20/0.54  % (6053)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (6057)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (6045)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (6053)Refutation not found, incomplete strategy% (6053)------------------------------
% 0.20/0.54  % (6053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6053)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6053)Memory used [KB]: 10746
% 0.20/0.54  % (6053)Time elapsed: 0.130 s
% 0.20/0.54  % (6053)------------------------------
% 0.20/0.54  % (6053)------------------------------
% 0.20/0.54  % (6055)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (6047)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (6048)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (6052)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.55  % (6046)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.51/0.56  % (6059)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.64/0.57  % (6048)Refutation found. Thanks to Tanya!
% 1.64/0.57  % SZS status Theorem for theBenchmark
% 1.64/0.57  % SZS output start Proof for theBenchmark
% 1.64/0.57  fof(f803,plain,(
% 1.64/0.57    $false),
% 1.64/0.57    inference(avatar_sat_refutation,[],[f108,f276,f279,f359,f361,f363,f366,f369,f439,f451,f453,f518,f595,f667,f694,f728,f745,f749,f750,f751,f802])).
% 1.64/0.57  fof(f802,plain,(
% 1.64/0.57    spl5_1 | ~spl5_3 | ~spl5_19),
% 1.64/0.57    inference(avatar_contradiction_clause,[],[f801])).
% 1.64/0.57  fof(f801,plain,(
% 1.64/0.57    $false | (spl5_1 | ~spl5_3 | ~spl5_19)),
% 1.64/0.57    inference(resolution,[],[f800,f167])).
% 1.64/0.57  fof(f167,plain,(
% 1.64/0.57    v2_funct_1(k1_xboole_0)),
% 1.64/0.57    inference(superposition,[],[f90,f134])).
% 1.64/0.57  fof(f134,plain,(
% 1.64/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.64/0.57    inference(resolution,[],[f130,f93])).
% 1.64/0.57  fof(f93,plain,(
% 1.64/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.64/0.57    inference(equality_resolution,[],[f68])).
% 1.64/0.57  fof(f68,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.64/0.57    inference(cnf_transformation,[],[f42])).
% 1.64/0.57  fof(f42,plain,(
% 1.64/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.57    inference(flattening,[],[f41])).
% 1.64/0.57  fof(f41,plain,(
% 1.64/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.57    inference(nnf_transformation,[],[f3])).
% 1.64/0.57  fof(f3,axiom,(
% 1.64/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.64/0.57  fof(f130,plain,(
% 1.64/0.57    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k6_partfun1(k1_xboole_0) = X1) )),
% 1.64/0.57    inference(resolution,[],[f121,f122])).
% 1.64/0.57  fof(f122,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.64/0.57    inference(resolution,[],[f118,f71])).
% 1.64/0.57  fof(f71,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f46])).
% 1.64/0.57  fof(f46,plain,(
% 1.64/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.64/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).
% 1.64/0.57  fof(f45,plain,(
% 1.64/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.64/0.57    introduced(choice_axiom,[])).
% 1.64/0.57  fof(f44,plain,(
% 1.64/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.64/0.57    inference(rectify,[],[f43])).
% 1.64/0.57  fof(f43,plain,(
% 1.64/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.64/0.57    inference(nnf_transformation,[],[f24])).
% 1.64/0.57  fof(f24,plain,(
% 1.64/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.64/0.57    inference(ennf_transformation,[],[f1])).
% 1.64/0.57  fof(f1,axiom,(
% 1.64/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.64/0.57  % (6064)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.64/0.59  fof(f118,plain,(
% 1.64/0.59    ( ! [X2,X1] : (~r2_hidden(X1,X2) | ~r1_tarski(X2,k1_xboole_0)) )),
% 1.64/0.59    inference(resolution,[],[f116,f74])).
% 1.64/0.59  fof(f74,plain,(
% 1.64/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f47])).
% 1.64/0.59  fof(f47,plain,(
% 1.64/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.64/0.59    inference(nnf_transformation,[],[f5])).
% 1.64/0.59  fof(f5,axiom,(
% 1.64/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.64/0.59  fof(f116,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 1.64/0.59    inference(resolution,[],[f83,f59])).
% 1.64/0.59  fof(f59,plain,(
% 1.64/0.59    v1_xboole_0(k1_xboole_0)),
% 1.64/0.59    inference(cnf_transformation,[],[f2])).
% 1.64/0.59  fof(f2,axiom,(
% 1.64/0.59    v1_xboole_0(k1_xboole_0)),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.64/0.59  fof(f83,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f30])).
% 1.64/0.59  fof(f30,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.64/0.59    inference(ennf_transformation,[],[f6])).
% 1.64/0.59  fof(f6,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.64/0.59  fof(f121,plain,(
% 1.64/0.59    ( ! [X0] : (~r1_tarski(X0,k6_partfun1(k1_xboole_0)) | k6_partfun1(k1_xboole_0) = X0) )),
% 1.64/0.59    inference(resolution,[],[f119,f69])).
% 1.64/0.59  fof(f69,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f42])).
% 1.64/0.59  fof(f119,plain,(
% 1.64/0.59    ( ! [X0] : (r1_tarski(k6_partfun1(k1_xboole_0),X0)) )),
% 1.64/0.59    inference(resolution,[],[f117,f71])).
% 1.64/0.59  fof(f117,plain,(
% 1.64/0.59    ( ! [X0] : (~r2_hidden(X0,k6_partfun1(k1_xboole_0))) )),
% 1.64/0.59    inference(resolution,[],[f116,f111])).
% 1.64/0.59  fof(f111,plain,(
% 1.64/0.59    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.64/0.59    inference(superposition,[],[f64,f95])).
% 1.64/0.59  fof(f95,plain,(
% 1.64/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.64/0.59    inference(equality_resolution,[],[f77])).
% 1.64/0.59  fof(f77,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.64/0.59    inference(cnf_transformation,[],[f49])).
% 1.64/0.59  fof(f49,plain,(
% 1.64/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.64/0.59    inference(flattening,[],[f48])).
% 1.64/0.59  fof(f48,plain,(
% 1.64/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.64/0.59    inference(nnf_transformation,[],[f4])).
% 1.64/0.59  fof(f4,axiom,(
% 1.64/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.64/0.59  fof(f64,plain,(
% 1.64/0.59    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f14])).
% 1.64/0.59  fof(f14,axiom,(
% 1.64/0.59    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.64/0.59  fof(f90,plain,(
% 1.64/0.59    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.64/0.59    inference(definition_unfolding,[],[f62,f60])).
% 1.64/0.59  fof(f60,plain,(
% 1.64/0.59    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f15])).
% 1.64/0.59  fof(f15,axiom,(
% 1.64/0.59    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.64/0.59  fof(f62,plain,(
% 1.64/0.59    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f7])).
% 1.64/0.59  fof(f7,axiom,(
% 1.64/0.59    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.64/0.59  fof(f800,plain,(
% 1.64/0.59    ~v2_funct_1(k1_xboole_0) | (spl5_1 | ~spl5_3 | ~spl5_19)),
% 1.64/0.59    inference(forward_demodulation,[],[f103,f794])).
% 1.64/0.59  fof(f794,plain,(
% 1.64/0.59    k1_xboole_0 = sK2 | (~spl5_3 | ~spl5_19)),
% 1.64/0.59    inference(forward_demodulation,[],[f793,f96])).
% 1.64/0.59  fof(f96,plain,(
% 1.64/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.64/0.59    inference(equality_resolution,[],[f76])).
% 1.64/0.59  fof(f76,plain,(
% 1.64/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.64/0.59    inference(cnf_transformation,[],[f49])).
% 1.64/0.59  fof(f793,plain,(
% 1.64/0.59    sK2 = k2_zfmisc_1(k1_xboole_0,sK1) | (~spl5_3 | ~spl5_19)),
% 1.64/0.59    inference(forward_demodulation,[],[f200,f420])).
% 1.64/0.59  fof(f420,plain,(
% 1.64/0.59    k1_xboole_0 = sK0 | ~spl5_19),
% 1.64/0.59    inference(avatar_component_clause,[],[f418])).
% 1.64/0.59  fof(f418,plain,(
% 1.64/0.59    spl5_19 <=> k1_xboole_0 = sK0),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.64/0.59  fof(f200,plain,(
% 1.64/0.59    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl5_3),
% 1.64/0.59    inference(avatar_component_clause,[],[f198])).
% 1.64/0.59  fof(f198,plain,(
% 1.64/0.59    spl5_3 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.64/0.59  fof(f103,plain,(
% 1.64/0.59    ~v2_funct_1(sK2) | spl5_1),
% 1.64/0.59    inference(avatar_component_clause,[],[f101])).
% 1.64/0.59  fof(f101,plain,(
% 1.64/0.59    spl5_1 <=> v2_funct_1(sK2)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.64/0.59  fof(f751,plain,(
% 1.64/0.59    spl5_3 | ~spl5_4),
% 1.64/0.59    inference(avatar_split_clause,[],[f538,f202,f198])).
% 1.64/0.59  fof(f202,plain,(
% 1.64/0.59    spl5_4 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.64/0.59  fof(f538,plain,(
% 1.64/0.59    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.64/0.59    inference(resolution,[],[f53,f115])).
% 1.64/0.59  fof(f115,plain,(
% 1.64/0.59    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~r1_tarski(X3,X4) | X3 = X4) )),
% 1.64/0.59    inference(resolution,[],[f69,f73])).
% 1.64/0.59  fof(f73,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f47])).
% 1.64/0.59  fof(f53,plain,(
% 1.64/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.64/0.59    inference(cnf_transformation,[],[f39])).
% 1.64/0.59  fof(f39,plain,(
% 1.64/0.59    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f38,f37])).
% 1.64/0.59  fof(f37,plain,(
% 1.64/0.59    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f38,plain,(
% 1.64/0.59    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f21,plain,(
% 1.64/0.59    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.64/0.59    inference(flattening,[],[f20])).
% 1.64/0.59  fof(f20,plain,(
% 1.64/0.59    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.64/0.59    inference(ennf_transformation,[],[f19])).
% 1.64/0.59  fof(f19,negated_conjecture,(
% 1.64/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.64/0.59    inference(negated_conjecture,[],[f18])).
% 1.64/0.59  fof(f18,conjecture,(
% 1.64/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.64/0.59  fof(f750,plain,(
% 1.64/0.59    ~spl5_12 | ~spl5_17 | ~spl5_13 | ~spl5_14 | ~spl5_18 | ~spl5_15 | spl5_1 | spl5_19 | ~spl5_20 | ~spl5_9),
% 1.64/0.59    inference(avatar_split_clause,[],[f585,f273,f422,f418,f101,f356,f414,f352,f348,f410,f344])).
% 1.64/0.59  fof(f344,plain,(
% 1.64/0.59    spl5_12 <=> v1_funct_1(sK2)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.64/0.59  fof(f410,plain,(
% 1.64/0.59    spl5_17 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.64/0.59  fof(f348,plain,(
% 1.64/0.59    spl5_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.64/0.59  fof(f352,plain,(
% 1.64/0.59    spl5_14 <=> v1_funct_1(sK3)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.64/0.59  fof(f414,plain,(
% 1.64/0.59    spl5_18 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.64/0.59  fof(f356,plain,(
% 1.64/0.59    spl5_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.64/0.59  fof(f422,plain,(
% 1.64/0.59    spl5_20 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.64/0.59  fof(f273,plain,(
% 1.64/0.59    spl5_9 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.64/0.59  fof(f585,plain,(
% 1.64/0.59    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl5_9),
% 1.64/0.59    inference(superposition,[],[f84,f275])).
% 1.64/0.59  fof(f275,plain,(
% 1.64/0.59    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl5_9),
% 1.64/0.59    inference(avatar_component_clause,[],[f273])).
% 1.64/0.59  fof(f84,plain,(
% 1.64/0.59    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f32])).
% 1.64/0.59  fof(f32,plain,(
% 1.64/0.59    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.64/0.59    inference(flattening,[],[f31])).
% 1.64/0.59  fof(f31,plain,(
% 1.64/0.59    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.64/0.59    inference(ennf_transformation,[],[f17])).
% 1.64/0.59  fof(f17,axiom,(
% 1.64/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.64/0.59  fof(f749,plain,(
% 1.64/0.59    spl5_31),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f746])).
% 1.64/0.59  fof(f746,plain,(
% 1.64/0.59    $false | spl5_31),
% 1.64/0.59    inference(resolution,[],[f740,f56])).
% 1.64/0.59  fof(f56,plain,(
% 1.64/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.64/0.59    inference(cnf_transformation,[],[f39])).
% 1.64/0.59  fof(f740,plain,(
% 1.64/0.59    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl5_31),
% 1.64/0.59    inference(resolution,[],[f727,f81])).
% 1.64/0.59  fof(f81,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f27])).
% 1.64/0.59  fof(f27,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.59    inference(ennf_transformation,[],[f9])).
% 1.64/0.59  fof(f9,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.64/0.59  fof(f727,plain,(
% 1.64/0.59    ~v5_relat_1(sK3,sK0) | spl5_31),
% 1.64/0.59    inference(avatar_component_clause,[],[f725])).
% 1.64/0.59  fof(f725,plain,(
% 1.64/0.59    spl5_31 <=> v5_relat_1(sK3,sK0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.64/0.59  fof(f745,plain,(
% 1.64/0.59    spl5_30),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f741])).
% 1.64/0.59  fof(f741,plain,(
% 1.64/0.59    $false | spl5_30),
% 1.64/0.59    inference(resolution,[],[f739,f56])).
% 1.64/0.59  fof(f739,plain,(
% 1.64/0.59    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_30),
% 1.64/0.59    inference(resolution,[],[f723,f78])).
% 1.64/0.59  fof(f78,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f25])).
% 1.64/0.59  fof(f25,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.59    inference(ennf_transformation,[],[f8])).
% 1.64/0.59  fof(f8,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.64/0.59  fof(f723,plain,(
% 1.64/0.59    ~v1_relat_1(sK3) | spl5_30),
% 1.64/0.59    inference(avatar_component_clause,[],[f721])).
% 1.64/0.59  fof(f721,plain,(
% 1.64/0.59    spl5_30 <=> v1_relat_1(sK3)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.64/0.59  fof(f728,plain,(
% 1.64/0.59    ~spl5_30 | ~spl5_31 | spl5_2 | ~spl5_27),
% 1.64/0.59    inference(avatar_split_clause,[],[f719,f610,f105,f725,f721])).
% 1.64/0.59  fof(f105,plain,(
% 1.64/0.59    spl5_2 <=> v2_funct_2(sK3,sK0)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.64/0.59  fof(f610,plain,(
% 1.64/0.59    spl5_27 <=> sK0 = k2_relat_1(sK3)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.64/0.59  fof(f719,plain,(
% 1.64/0.59    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl5_27),
% 1.64/0.59    inference(superposition,[],[f92,f611])).
% 1.64/0.59  fof(f611,plain,(
% 1.64/0.59    sK0 = k2_relat_1(sK3) | ~spl5_27),
% 1.64/0.59    inference(avatar_component_clause,[],[f610])).
% 1.64/0.59  fof(f92,plain,(
% 1.64/0.59    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.64/0.59    inference(equality_resolution,[],[f66])).
% 1.64/0.59  fof(f66,plain,(
% 1.64/0.59    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f40])).
% 1.64/0.59  fof(f40,plain,(
% 1.64/0.59    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/0.59    inference(nnf_transformation,[],[f23])).
% 1.64/0.59  fof(f23,plain,(
% 1.64/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/0.59    inference(flattening,[],[f22])).
% 1.64/0.59  fof(f22,plain,(
% 1.64/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.64/0.59    inference(ennf_transformation,[],[f12])).
% 1.64/0.59  fof(f12,axiom,(
% 1.64/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.64/0.59  fof(f694,plain,(
% 1.64/0.59    ~spl5_15 | spl5_27 | ~spl5_23),
% 1.64/0.59    inference(avatar_split_clause,[],[f692,f588,f610,f356])).
% 1.64/0.59  fof(f588,plain,(
% 1.64/0.59    spl5_23 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.64/0.59  fof(f692,plain,(
% 1.64/0.59    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_23),
% 1.64/0.59    inference(superposition,[],[f79,f590])).
% 1.64/0.59  fof(f590,plain,(
% 1.64/0.59    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl5_23),
% 1.64/0.59    inference(avatar_component_clause,[],[f588])).
% 1.64/0.59  fof(f79,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f26])).
% 1.64/0.59  fof(f26,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.59    inference(ennf_transformation,[],[f10])).
% 1.64/0.59  fof(f10,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.64/0.59  fof(f667,plain,(
% 1.64/0.59    ~spl5_9 | spl5_24),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f665])).
% 1.64/0.59  fof(f665,plain,(
% 1.64/0.59    $false | (~spl5_9 | spl5_24)),
% 1.64/0.59    inference(resolution,[],[f594,f370])).
% 1.64/0.59  fof(f370,plain,(
% 1.64/0.59    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~spl5_9),
% 1.64/0.59    inference(backward_demodulation,[],[f57,f275])).
% 1.64/0.59  fof(f57,plain,(
% 1.64/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.64/0.59    inference(cnf_transformation,[],[f39])).
% 1.64/0.59  fof(f594,plain,(
% 1.64/0.59    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl5_24),
% 1.64/0.59    inference(avatar_component_clause,[],[f592])).
% 1.64/0.59  fof(f592,plain,(
% 1.64/0.59    spl5_24 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.64/0.59  fof(f595,plain,(
% 1.64/0.59    ~spl5_14 | ~spl5_18 | ~spl5_15 | ~spl5_12 | ~spl5_17 | ~spl5_13 | spl5_23 | ~spl5_24 | ~spl5_9),
% 1.64/0.59    inference(avatar_split_clause,[],[f586,f273,f592,f588,f348,f410,f344,f356,f414,f352])).
% 1.64/0.59  fof(f586,plain,(
% 1.64/0.59    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl5_9),
% 1.64/0.59    inference(superposition,[],[f82,f275])).
% 1.64/0.59  fof(f82,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f29])).
% 1.64/0.59  fof(f29,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.64/0.59    inference(flattening,[],[f28])).
% 1.64/0.59  fof(f28,plain,(
% 1.64/0.59    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.64/0.59    inference(ennf_transformation,[],[f16])).
% 1.64/0.59  fof(f16,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.64/0.59  fof(f518,plain,(
% 1.64/0.59    spl5_4 | ~spl5_19),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f513])).
% 1.64/0.59  fof(f513,plain,(
% 1.64/0.59    $false | (spl5_4 | ~spl5_19)),
% 1.64/0.59    inference(resolution,[],[f488,f142])).
% 1.64/0.59  fof(f142,plain,(
% 1.64/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.64/0.59    inference(backward_demodulation,[],[f119,f134])).
% 1.64/0.59  fof(f488,plain,(
% 1.64/0.59    ~r1_tarski(k1_xboole_0,sK2) | (spl5_4 | ~spl5_19)),
% 1.64/0.59    inference(forward_demodulation,[],[f460,f96])).
% 1.64/0.59  fof(f460,plain,(
% 1.64/0.59    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK2) | (spl5_4 | ~spl5_19)),
% 1.64/0.59    inference(backward_demodulation,[],[f204,f420])).
% 1.64/0.59  fof(f204,plain,(
% 1.64/0.59    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl5_4),
% 1.64/0.59    inference(avatar_component_clause,[],[f202])).
% 1.64/0.59  fof(f453,plain,(
% 1.64/0.59    spl5_18),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f452])).
% 1.64/0.59  fof(f452,plain,(
% 1.64/0.59    $false | spl5_18),
% 1.64/0.59    inference(resolution,[],[f416,f55])).
% 1.64/0.59  fof(f55,plain,(
% 1.64/0.59    v1_funct_2(sK3,sK1,sK0)),
% 1.64/0.59    inference(cnf_transformation,[],[f39])).
% 1.64/0.59  fof(f416,plain,(
% 1.64/0.59    ~v1_funct_2(sK3,sK1,sK0) | spl5_18),
% 1.64/0.59    inference(avatar_component_clause,[],[f414])).
% 1.64/0.59  fof(f451,plain,(
% 1.64/0.59    spl5_17),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f450])).
% 1.64/0.59  fof(f450,plain,(
% 1.64/0.59    $false | spl5_17),
% 1.64/0.59    inference(resolution,[],[f412,f52])).
% 1.64/0.59  fof(f52,plain,(
% 1.64/0.59    v1_funct_2(sK2,sK0,sK1)),
% 1.64/0.59    inference(cnf_transformation,[],[f39])).
% 1.64/0.59  fof(f412,plain,(
% 1.64/0.59    ~v1_funct_2(sK2,sK0,sK1) | spl5_17),
% 1.64/0.59    inference(avatar_component_clause,[],[f410])).
% 1.64/0.59  fof(f439,plain,(
% 1.64/0.59    spl5_20),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f438])).
% 1.64/0.59  fof(f438,plain,(
% 1.64/0.59    $false | spl5_20),
% 1.64/0.59    inference(resolution,[],[f424,f90])).
% 1.64/0.59  fof(f424,plain,(
% 1.64/0.59    ~v2_funct_1(k6_partfun1(sK0)) | spl5_20),
% 1.64/0.59    inference(avatar_component_clause,[],[f422])).
% 1.64/0.59  fof(f369,plain,(
% 1.64/0.59    spl5_15),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f367])).
% 1.64/0.59  fof(f367,plain,(
% 1.64/0.59    $false | spl5_15),
% 1.64/0.59    inference(resolution,[],[f358,f56])).
% 1.64/0.59  fof(f358,plain,(
% 1.64/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_15),
% 1.64/0.59    inference(avatar_component_clause,[],[f356])).
% 1.64/0.59  fof(f366,plain,(
% 1.64/0.59    spl5_13),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f364])).
% 1.64/0.59  fof(f364,plain,(
% 1.64/0.59    $false | spl5_13),
% 1.64/0.59    inference(resolution,[],[f350,f53])).
% 1.64/0.59  fof(f350,plain,(
% 1.64/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_13),
% 1.64/0.59    inference(avatar_component_clause,[],[f348])).
% 1.64/0.59  fof(f363,plain,(
% 1.64/0.59    spl5_14),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f362])).
% 1.64/0.59  fof(f362,plain,(
% 1.64/0.59    $false | spl5_14),
% 1.64/0.59    inference(resolution,[],[f354,f54])).
% 1.64/0.59  fof(f54,plain,(
% 1.64/0.59    v1_funct_1(sK3)),
% 1.64/0.59    inference(cnf_transformation,[],[f39])).
% 1.64/0.59  fof(f354,plain,(
% 1.64/0.59    ~v1_funct_1(sK3) | spl5_14),
% 1.64/0.59    inference(avatar_component_clause,[],[f352])).
% 1.64/0.59  fof(f361,plain,(
% 1.64/0.59    spl5_12),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f360])).
% 1.64/0.59  fof(f360,plain,(
% 1.64/0.59    $false | spl5_12),
% 1.64/0.59    inference(resolution,[],[f346,f51])).
% 1.64/0.59  fof(f51,plain,(
% 1.64/0.59    v1_funct_1(sK2)),
% 1.64/0.59    inference(cnf_transformation,[],[f39])).
% 1.64/0.59  fof(f346,plain,(
% 1.64/0.59    ~v1_funct_1(sK2) | spl5_12),
% 1.64/0.59    inference(avatar_component_clause,[],[f344])).
% 1.64/0.59  fof(f359,plain,(
% 1.64/0.59    ~spl5_12 | ~spl5_13 | ~spl5_14 | ~spl5_15 | spl5_7),
% 1.64/0.59    inference(avatar_split_clause,[],[f341,f265,f356,f352,f348,f344])).
% 1.64/0.59  fof(f265,plain,(
% 1.64/0.59    spl5_7 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.64/0.59  fof(f341,plain,(
% 1.64/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl5_7),
% 1.64/0.59    inference(resolution,[],[f267,f89])).
% 1.64/0.59  fof(f89,plain,(
% 1.64/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f36])).
% 1.64/0.59  fof(f36,plain,(
% 1.64/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.64/0.59    inference(flattening,[],[f35])).
% 1.64/0.59  fof(f35,plain,(
% 1.64/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.64/0.59    inference(ennf_transformation,[],[f13])).
% 1.64/0.59  fof(f13,axiom,(
% 1.64/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.64/0.59  fof(f267,plain,(
% 1.64/0.59    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_7),
% 1.64/0.59    inference(avatar_component_clause,[],[f265])).
% 1.64/0.59  fof(f279,plain,(
% 1.64/0.59    spl5_8),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f277])).
% 1.64/0.59  fof(f277,plain,(
% 1.64/0.59    $false | spl5_8),
% 1.64/0.59    inference(resolution,[],[f271,f64])).
% 1.64/0.59  fof(f271,plain,(
% 1.64/0.59    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_8),
% 1.64/0.59    inference(avatar_component_clause,[],[f269])).
% 1.64/0.59  fof(f269,plain,(
% 1.64/0.59    spl5_8 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.64/0.59  fof(f276,plain,(
% 1.64/0.59    ~spl5_7 | ~spl5_8 | spl5_9),
% 1.64/0.59    inference(avatar_split_clause,[],[f261,f273,f269,f265])).
% 1.64/0.59  fof(f261,plain,(
% 1.64/0.59    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.64/0.59    inference(resolution,[],[f86,f57])).
% 1.64/0.59  fof(f86,plain,(
% 1.64/0.59    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/0.59    inference(cnf_transformation,[],[f50])).
% 1.64/0.59  fof(f50,plain,(
% 1.64/0.59    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.59    inference(nnf_transformation,[],[f34])).
% 1.64/0.59  fof(f34,plain,(
% 1.64/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.59    inference(flattening,[],[f33])).
% 1.64/0.59  fof(f33,plain,(
% 1.64/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.64/0.59    inference(ennf_transformation,[],[f11])).
% 1.64/0.59  fof(f11,axiom,(
% 1.64/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.64/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.64/0.59  fof(f108,plain,(
% 1.64/0.59    ~spl5_1 | ~spl5_2),
% 1.64/0.59    inference(avatar_split_clause,[],[f58,f105,f101])).
% 1.64/0.59  fof(f58,plain,(
% 1.64/0.59    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.64/0.59    inference(cnf_transformation,[],[f39])).
% 1.64/0.59  % SZS output end Proof for theBenchmark
% 1.64/0.59  % (6048)------------------------------
% 1.64/0.59  % (6048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (6048)Termination reason: Refutation
% 1.64/0.59  
% 1.64/0.59  % (6048)Memory used [KB]: 6524
% 1.64/0.59  % (6048)Time elapsed: 0.173 s
% 1.64/0.59  % (6048)------------------------------
% 1.64/0.59  % (6048)------------------------------
% 1.64/0.59  % (6035)Success in time 0.238 s
%------------------------------------------------------------------------------
