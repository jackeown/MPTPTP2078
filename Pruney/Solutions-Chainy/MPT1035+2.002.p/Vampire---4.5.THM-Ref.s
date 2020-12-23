%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  193 (1216 expanded)
%              Number of leaves         :   24 ( 363 expanded)
%              Depth                    :   32
%              Number of atoms          :  926 (10229 expanded)
%              Number of equality atoms :  161 (3021 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f839,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f94,f103,f236,f252,f257,f291,f446,f481,f838])).

fof(f838,plain,
    ( spl7_1
    | ~ spl7_4
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f837])).

fof(f837,plain,
    ( $false
    | spl7_1
    | ~ spl7_4
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f836,f158])).

fof(f158,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(resolution,[],[f155,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f155,plain,(
    ! [X0] :
      ( r2_hidden(sK6(k1_relat_1(sK2),X0),sK0)
      | r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f152,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f152,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f149,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f149,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f148,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
        & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) )
      | ~ r1_partfun1(sK2,sK3) )
    & ( ! [X5] :
          ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
      | r1_partfun1(sK2,sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X3,X4) != k1_funct_1(sK2,X4)
                & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
            | ~ r1_partfun1(sK2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X3,X5) = k1_funct_1(sK2,X5)
                | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
            | r1_partfun1(sK2,X3) )
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( ? [X4] :
              ( k1_funct_1(X3,X4) != k1_funct_1(sK2,X4)
              & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
          | ~ r1_partfun1(sK2,X3) )
        & ( ! [X5] :
              ( k1_funct_1(X3,X5) = k1_funct_1(sK2,X5)
              | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
          | r1_partfun1(sK2,X3) )
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ( ? [X4] :
            ( k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4)
            & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
        | ~ r1_partfun1(sK2,sK3) )
      & ( ! [X5] :
            ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
        | r1_partfun1(sK2,sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X4] :
        ( k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4)
        & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) )
   => ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
      & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ r1_partfun1(X2,X3) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).

fof(f148,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f63,f106])).

fof(f106,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f42,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f836,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f835,f606])).

fof(f606,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f125,f256])).

fof(f256,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f254])).

% (14704)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f254,plain,
    ( spl7_18
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f125,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f45,f62])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f835,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | spl7_1
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f834,f107])).

fof(f107,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f42,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f834,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f833,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f833,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f832,f126])).

fof(f126,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f45,f61])).

fof(f832,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f831,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f831,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f830,f80])).

fof(f80,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl7_1
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f830,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(trivial_inequality_removal,[],[f829])).

fof(f829,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK2,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(superposition,[],[f53,f787])).

fof(f787,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(resolution,[],[f235,f774])).

fof(f774,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK2))
        | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) )
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f93,f664])).

fof(f664,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f42,f62])).

fof(f93,plain,
    ( ! [X5] :
        ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
        | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl7_4
  <=> ! [X5] :
        ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
        | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f235,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl7_17
  <=> r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | r1_partfun1(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
                & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) ) )
            & ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).

fof(f481,plain,
    ( spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f479,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f479,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f478,f323])).

fof(f323,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f296,f322])).

fof(f322,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f321,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f321,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f113,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f113,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_7
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f296,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f261,f97])).

fof(f261,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f106,f102])).

fof(f478,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f477,f376])).

fof(f376,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f300,f373])).

fof(f373,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f365,f294])).

fof(f294,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f259,f97])).

fof(f259,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f44,f102])).

fof(f44,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f365,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f295,f76])).

% (14689)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f76,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

% (14686)Refutation not found, incomplete strategy% (14686)------------------------------
% (14686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

% (14686)Termination reason: Refutation not found, incomplete strategy

% (14686)Memory used [KB]: 10746
% (14686)Time elapsed: 0.161 s
% (14686)------------------------------
% (14686)------------------------------
fof(f295,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f260,f97])).

fof(f260,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f45,f102])).

fof(f300,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f265,f97])).

fof(f265,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f125,f102])).

fof(f477,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f476,f107])).

fof(f476,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f475,f41])).

fof(f475,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f474,f126])).

fof(f474,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f473,f43])).

fof(f473,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f472,f80])).

fof(f472,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(trivial_inequality_removal,[],[f471])).

fof(f471,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK2,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(superposition,[],[f53,f464])).

fof(f464,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f455,f451])).

fof(f451,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_xboole_0)
        | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f450,f322])).

fof(f450,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
        | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f449,f102])).

fof(f449,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relset_1(sK0,k1_xboole_0,sK2))
        | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) )
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f93,f97])).

fof(f455,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_xboole_0)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f454,f126])).

fof(f454,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f411,f80])).

fof(f411,plain,
    ( r1_partfun1(sK2,sK3)
    | r2_hidden(sK5(sK2,sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f362,f43])).

fof(f362,plain,
    ( ! [X4] :
        ( ~ v1_funct_1(X4)
        | r1_partfun1(sK2,X4)
        | r2_hidden(sK5(sK2,X4),k1_xboole_0)
        | ~ v1_relat_1(X4) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f361,f107])).

fof(f361,plain,
    ( ! [X4] :
        ( r2_hidden(sK5(sK2,X4),k1_xboole_0)
        | r1_partfun1(sK2,X4)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f360,f41])).

fof(f360,plain,
    ( ! [X4] :
        ( r2_hidden(sK5(sK2,X4),k1_xboole_0)
        | r1_partfun1(sK2,X4)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f353,f50])).

fof(f353,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X4))
        | r2_hidden(sK5(sK2,X4),k1_xboole_0)
        | r1_partfun1(sK2,X4)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(superposition,[],[f52,f323])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f446,plain,
    ( ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f442,f84])).

fof(f84,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_2
  <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f442,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f437,f292])).

fof(f292,plain,
    ( ! [X0] : r2_hidden(sK4,X0)
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f286,f50])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r2_hidden(sK4,X0) )
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f243,f102])).

fof(f243,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,X0)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f238,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f238,plain,
    ( r2_hidden(sK4,sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f237,f152])).

fof(f237,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f89,f106])).

fof(f89,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_3
  <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f437,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f436,f126])).

fof(f436,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f434,f43])).

fof(f434,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f357,f79])).

fof(f79,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f357,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(sK2,X0)
        | ~ r2_hidden(X1,k1_xboole_0)
        | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f356,f107])).

fof(f356,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_partfun1(sK2,X0)
        | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f355,f41])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_partfun1(sK2,X0)
        | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f351,f50])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_partfun1(sK2,X0)
        | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(superposition,[],[f51,f323])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r1_partfun1(X0,X1)
      | k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f291,plain,
    ( ~ spl7_6
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl7_6
    | spl7_7 ),
    inference(subsumption_resolution,[],[f277,f50])).

fof(f277,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2))
    | ~ spl7_6
    | spl7_7 ),
    inference(backward_demodulation,[],[f167,f102])).

fof(f167,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | spl7_7 ),
    inference(subsumption_resolution,[],[f166,f147])).

fof(f147,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl7_7 ),
    inference(superposition,[],[f112,f106])).

fof(f112,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f166,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f158,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f257,plain,
    ( spl7_18
    | spl7_5 ),
    inference(avatar_split_clause,[],[f128,f96,f254])).

fof(f128,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f123,f44])).

fof(f123,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f45,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f252,plain,
    ( ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f250,f107])).

fof(f250,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f249,f41])).

fof(f249,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f248,f84])).

fof(f248,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f247,f79])).

fof(f247,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f245,f158])).

fof(f245,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ r1_partfun1(sK2,sK3)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | spl7_5 ),
    inference(resolution,[],[f136,f237])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ r1_tarski(k1_relat_1(X0),sK0)
        | ~ r1_partfun1(X0,sK3)
        | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl7_5 ),
    inference(subsumption_resolution,[],[f135,f126])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),sK0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ r1_partfun1(X0,sK3)
        | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl7_5 ),
    inference(subsumption_resolution,[],[f131,f43])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),sK0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ r1_partfun1(X0,sK3)
        | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | spl7_5 ),
    inference(superposition,[],[f51,f130])).

fof(f130,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl7_5 ),
    inference(forward_demodulation,[],[f125,f129])).

fof(f129,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl7_5 ),
    inference(subsumption_resolution,[],[f128,f98])).

fof(f98,plain,
    ( k1_xboole_0 != sK1
    | spl7_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f236,plain,
    ( spl7_1
    | spl7_17
    | spl7_5 ),
    inference(avatar_split_clause,[],[f231,f96,f233,f78])).

fof(f231,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | spl7_5 ),
    inference(subsumption_resolution,[],[f230,f107])).

fof(f230,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ v1_relat_1(sK2)
    | spl7_5 ),
    inference(subsumption_resolution,[],[f209,f41])).

fof(f209,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_5 ),
    inference(resolution,[],[f140,f158])).

fof(f140,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(X4),sK0)
        | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
        | r1_partfun1(X4,sK3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | spl7_5 ),
    inference(subsumption_resolution,[],[f139,f126])).

fof(f139,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(X4),sK0)
        | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
        | r1_partfun1(X4,sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | spl7_5 ),
    inference(subsumption_resolution,[],[f133,f43])).

fof(f133,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(X4),sK0)
        | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
        | r1_partfun1(X4,sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | spl7_5 ),
    inference(superposition,[],[f52,f130])).

fof(f103,plain,
    ( ~ spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f46,f100,f96])).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f47,f92,f78])).

fof(f47,plain,(
    ! [X5] :
      ( k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f48,f87,f78])).

fof(f48,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f49,f82,f78])).

fof(f49,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (14692)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (14676)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (14684)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (14688)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (14696)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (14677)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (14683)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (14698)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (14679)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (14678)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (14680)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (14690)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (14695)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (14681)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (14699)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (14700)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (14682)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (14703)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (14702)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (14697)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (14705)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (14701)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (14691)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (14693)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (14694)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (14685)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (14687)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (14686)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (14684)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f839,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f85,f90,f94,f103,f236,f252,f257,f291,f446,f481,f838])).
% 0.20/0.56  fof(f838,plain,(
% 0.20/0.56    spl7_1 | ~spl7_4 | ~spl7_17 | ~spl7_18),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f837])).
% 0.20/0.56  fof(f837,plain,(
% 0.20/0.56    $false | (spl7_1 | ~spl7_4 | ~spl7_17 | ~spl7_18)),
% 0.20/0.56    inference(subsumption_resolution,[],[f836,f158])).
% 0.20/0.56  fof(f158,plain,(
% 0.20/0.56    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f156])).
% 0.20/0.56  fof(f156,plain,(
% 0.20/0.56    r1_tarski(k1_relat_1(sK2),sK0) | r1_tarski(k1_relat_1(sK2),sK0)),
% 0.20/0.56    inference(resolution,[],[f155,f60])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f155,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK6(k1_relat_1(sK2),X0),sK0) | r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.20/0.56    inference(resolution,[],[f152,f59])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f39])).
% 0.20/0.56  fof(f152,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(X0,sK0)) )),
% 0.20/0.56    inference(resolution,[],[f149,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.56  fof(f149,plain,(
% 0.20/0.56    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.20/0.56    inference(subsumption_resolution,[],[f148,f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    (((k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f28,f27,f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : ((? [X4] : (k1_funct_1(X3,X4) != k1_funct_1(sK2,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,X3)) & (! [X5] : (k1_funct_1(X3,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,X3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ? [X3] : ((? [X4] : (k1_funct_1(X3,X4) != k1_funct_1(sK2,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,X3)) & (! [X5] : (k1_funct_1(X3,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,X3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => ((? [X4] : (k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) | ~r1_partfun1(sK2,sK3)) & (! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) | r1_partfun1(sK2,sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ? [X4] : (k1_funct_1(sK2,X4) != k1_funct_1(sK3,X4) & r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))) => (k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) & r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~r2_hidden(X5,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.56    inference(rectify,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : ((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.56    inference(flattening,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : (((? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,k1_relset_1(X0,X1,X2))) | ~r1_partfun1(X2,X3)) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2))) | r1_partfun1(X2,X3))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.56    inference(nnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.56    inference(flattening,[],[f12])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.20/0.56    inference(negated_conjecture,[],[f10])).
% 0.20/0.56  fof(f10,conjecture,(
% 0.20/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_2)).
% 0.20/0.56  fof(f148,plain,(
% 0.20/0.56    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    inference(superposition,[],[f63,f106])).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.56    inference(resolution,[],[f42,f62])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.56  fof(f836,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),sK0) | (spl7_1 | ~spl7_4 | ~spl7_17 | ~spl7_18)),
% 0.20/0.56    inference(forward_demodulation,[],[f835,f606])).
% 0.20/0.56  fof(f606,plain,(
% 0.20/0.56    sK0 = k1_relat_1(sK3) | ~spl7_18),
% 0.20/0.56    inference(forward_demodulation,[],[f125,f256])).
% 0.20/0.56  fof(f256,plain,(
% 0.20/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_18),
% 0.20/0.56    inference(avatar_component_clause,[],[f254])).
% 0.20/0.56  % (14704)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  fof(f254,plain,(
% 0.20/0.56    spl7_18 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.56  fof(f125,plain,(
% 0.20/0.56    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.56    inference(resolution,[],[f45,f62])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f835,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | (spl7_1 | ~spl7_4 | ~spl7_17)),
% 0.20/0.56    inference(subsumption_resolution,[],[f834,f107])).
% 0.20/0.56  fof(f107,plain,(
% 0.20/0.56    v1_relat_1(sK2)),
% 0.20/0.56    inference(resolution,[],[f42,f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.56  fof(f834,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_17)),
% 0.20/0.56    inference(subsumption_resolution,[],[f833,f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    v1_funct_1(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f833,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_17)),
% 0.20/0.56    inference(subsumption_resolution,[],[f832,f126])).
% 0.20/0.56  fof(f126,plain,(
% 0.20/0.56    v1_relat_1(sK3)),
% 0.20/0.56    inference(resolution,[],[f45,f61])).
% 0.20/0.56  fof(f832,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_17)),
% 0.20/0.56    inference(subsumption_resolution,[],[f831,f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    v1_funct_1(sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f831,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_17)),
% 0.20/0.56    inference(subsumption_resolution,[],[f830,f80])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    ~r1_partfun1(sK2,sK3) | spl7_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f78])).
% 0.20/0.56  fof(f78,plain,(
% 0.20/0.56    spl7_1 <=> r1_partfun1(sK2,sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.56  fof(f830,plain,(
% 0.20/0.56    r1_partfun1(sK2,sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_4 | ~spl7_17)),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f829])).
% 0.20/0.56  fof(f829,plain,(
% 0.20/0.56    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK2,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_4 | ~spl7_17)),
% 0.20/0.56    inference(superposition,[],[f53,f787])).
% 0.20/0.56  fof(f787,plain,(
% 0.20/0.56    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | (~spl7_4 | ~spl7_17)),
% 0.20/0.56    inference(resolution,[],[f235,f774])).
% 0.20/0.56  fof(f774,plain,(
% 0.20/0.56    ( ! [X5] : (~r2_hidden(X5,k1_relat_1(sK2)) | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)) ) | ~spl7_4),
% 0.20/0.56    inference(forward_demodulation,[],[f93,f664])).
% 0.20/0.56  fof(f664,plain,(
% 0.20/0.56    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.56    inference(resolution,[],[f42,f62])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    ( ! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2))) ) | ~spl7_4),
% 0.20/0.56    inference(avatar_component_clause,[],[f92])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    spl7_4 <=> ! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.56  fof(f235,plain,(
% 0.20/0.56    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | ~spl7_17),
% 0.20/0.56    inference(avatar_component_clause,[],[f233])).
% 0.20/0.56  fof(f233,plain,(
% 0.20/0.56    spl7_17 <=> r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | r1_partfun1(X0,X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(rectify,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0)))) & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) | ~r1_partfun1(X0,X1))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_partfun1)).
% 0.20/0.56  fof(f481,plain,(
% 0.20/0.56    spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f480])).
% 0.20/0.56  fof(f480,plain,(
% 0.20/0.56    $false | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f479,f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.56  fof(f479,plain,(
% 0.20/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(forward_demodulation,[],[f478,f323])).
% 0.20/0.56  fof(f323,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(sK2) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(backward_demodulation,[],[f296,f322])).
% 0.20/0.56  fof(f322,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(forward_demodulation,[],[f321,f102])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | ~spl7_6),
% 0.20/0.56    inference(avatar_component_clause,[],[f100])).
% 0.20/0.56  fof(f100,plain,(
% 0.20/0.56    spl7_6 <=> k1_xboole_0 = sK0),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.56  fof(f321,plain,(
% 0.20/0.56    sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) | (~spl7_5 | ~spl7_7)),
% 0.20/0.56    inference(forward_demodulation,[],[f113,f97])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    k1_xboole_0 = sK1 | ~spl7_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f96])).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    spl7_5 <=> k1_xboole_0 = sK1),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.56  fof(f113,plain,(
% 0.20/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_7),
% 0.20/0.56    inference(avatar_component_clause,[],[f111])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    spl7_7 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.56  fof(f296,plain,(
% 0.20/0.56    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_5 | ~spl7_6)),
% 0.20/0.56    inference(backward_demodulation,[],[f261,f97])).
% 0.20/0.56  fof(f261,plain,(
% 0.20/0.56    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2) | ~spl7_6),
% 0.20/0.56    inference(backward_demodulation,[],[f106,f102])).
% 0.20/0.56  fof(f478,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(forward_demodulation,[],[f477,f376])).
% 0.20/0.56  fof(f376,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relat_1(sK3) | (~spl7_5 | ~spl7_6)),
% 0.20/0.56    inference(backward_demodulation,[],[f300,f373])).
% 0.20/0.56  fof(f373,plain,(
% 0.20/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_5 | ~spl7_6)),
% 0.20/0.56    inference(subsumption_resolution,[],[f365,f294])).
% 0.20/0.56  fof(f294,plain,(
% 0.20/0.56    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_5 | ~spl7_6)),
% 0.20/0.56    inference(backward_demodulation,[],[f259,f97])).
% 0.20/0.56  fof(f259,plain,(
% 0.20/0.56    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl7_6),
% 0.20/0.56    inference(backward_demodulation,[],[f44,f102])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f365,plain,(
% 0.20/0.56    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_5 | ~spl7_6)),
% 0.20/0.56    inference(resolution,[],[f295,f76])).
% 0.20/0.56  % (14689)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  fof(f76,plain,(
% 0.20/0.56    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.20/0.56    inference(equality_resolution,[],[f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(nnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(flattening,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  % (14686)Refutation not found, incomplete strategy% (14686)------------------------------
% 0.20/0.56  % (14686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.56  % (14686)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (14686)Memory used [KB]: 10746
% 0.20/0.56  % (14686)Time elapsed: 0.161 s
% 0.20/0.56  % (14686)------------------------------
% 0.20/0.56  % (14686)------------------------------
% 0.20/0.56  fof(f295,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_5 | ~spl7_6)),
% 0.20/0.56    inference(backward_demodulation,[],[f260,f97])).
% 0.20/0.56  fof(f260,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl7_6),
% 0.20/0.56    inference(backward_demodulation,[],[f45,f102])).
% 0.20/0.56  fof(f300,plain,(
% 0.20/0.56    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_5 | ~spl7_6)),
% 0.20/0.56    inference(backward_demodulation,[],[f265,f97])).
% 0.20/0.56  fof(f265,plain,(
% 0.20/0.56    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3) | ~spl7_6),
% 0.20/0.56    inference(backward_demodulation,[],[f125,f102])).
% 0.20/0.56  fof(f477,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f476,f107])).
% 0.20/0.56  fof(f476,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f475,f41])).
% 0.20/0.56  fof(f475,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f474,f126])).
% 0.20/0.56  fof(f474,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f473,f43])).
% 0.20/0.56  fof(f473,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f472,f80])).
% 0.20/0.56  fof(f472,plain,(
% 0.20/0.56    r1_partfun1(sK2,sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f471])).
% 0.20/0.56  fof(f471,plain,(
% 0.20/0.56    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK2,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(superposition,[],[f53,f464])).
% 0.20/0.56  fof(f464,plain,(
% 0.20/0.56    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(resolution,[],[f455,f451])).
% 0.20/0.56  fof(f451,plain,(
% 0.20/0.56    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)) ) | (~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(forward_demodulation,[],[f450,f322])).
% 0.20/0.56  fof(f450,plain,(
% 0.20/0.56    ( ! [X5] : (~r2_hidden(X5,k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)) ) | (~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.56    inference(forward_demodulation,[],[f449,f102])).
% 0.20/0.56  fof(f449,plain,(
% 0.20/0.56    ( ! [X5] : (~r2_hidden(X5,k1_relset_1(sK0,k1_xboole_0,sK2)) | k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5)) ) | (~spl7_4 | ~spl7_5)),
% 0.20/0.56    inference(forward_demodulation,[],[f93,f97])).
% 0.20/0.56  fof(f455,plain,(
% 0.20/0.56    r2_hidden(sK5(sK2,sK3),k1_xboole_0) | (spl7_1 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f454,f126])).
% 0.20/0.56  fof(f454,plain,(
% 0.20/0.56    r2_hidden(sK5(sK2,sK3),k1_xboole_0) | ~v1_relat_1(sK3) | (spl7_1 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f411,f80])).
% 0.20/0.56  fof(f411,plain,(
% 0.20/0.56    r1_partfun1(sK2,sK3) | r2_hidden(sK5(sK2,sK3),k1_xboole_0) | ~v1_relat_1(sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(resolution,[],[f362,f43])).
% 0.20/0.56  fof(f362,plain,(
% 0.20/0.56    ( ! [X4] : (~v1_funct_1(X4) | r1_partfun1(sK2,X4) | r2_hidden(sK5(sK2,X4),k1_xboole_0) | ~v1_relat_1(X4)) ) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f361,f107])).
% 0.20/0.56  fof(f361,plain,(
% 0.20/0.56    ( ! [X4] : (r2_hidden(sK5(sK2,X4),k1_xboole_0) | r1_partfun1(sK2,X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_relat_1(sK2)) ) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f360,f41])).
% 0.20/0.56  fof(f360,plain,(
% 0.20/0.56    ( ! [X4] : (r2_hidden(sK5(sK2,X4),k1_xboole_0) | r1_partfun1(sK2,X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f353,f50])).
% 0.20/0.56  fof(f353,plain,(
% 0.20/0.56    ( ! [X4] : (~r1_tarski(k1_xboole_0,k1_relat_1(X4)) | r2_hidden(sK5(sK2,X4),k1_xboole_0) | r1_partfun1(sK2,X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(superposition,[],[f52,f323])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r1_partfun1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f446,plain,(
% 0.20/0.56    ~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f445])).
% 0.20/0.56  fof(f445,plain,(
% 0.20/0.56    $false | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f442,f84])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | spl7_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f82])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    spl7_2 <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.56  fof(f442,plain,(
% 0.20/0.56    k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | (~spl7_1 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(resolution,[],[f437,f292])).
% 0.20/0.56  fof(f292,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK4,X0)) ) | (~spl7_3 | ~spl7_6)),
% 0.20/0.56    inference(subsumption_resolution,[],[f286,f50])).
% 0.20/0.56  fof(f286,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r2_hidden(sK4,X0)) ) | (~spl7_3 | ~spl7_6)),
% 0.20/0.56    inference(backward_demodulation,[],[f243,f102])).
% 0.20/0.56  fof(f243,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK4,X0) | ~r1_tarski(sK0,X0)) ) | ~spl7_3),
% 0.20/0.56    inference(resolution,[],[f238,f58])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f39])).
% 0.20/0.56  fof(f238,plain,(
% 0.20/0.56    r2_hidden(sK4,sK0) | ~spl7_3),
% 0.20/0.56    inference(resolution,[],[f237,f152])).
% 0.20/0.56  fof(f237,plain,(
% 0.20/0.56    r2_hidden(sK4,k1_relat_1(sK2)) | ~spl7_3),
% 0.20/0.56    inference(forward_demodulation,[],[f89,f106])).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~spl7_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f87])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    spl7_3 <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.56  fof(f437,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)) ) | (~spl7_1 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f436,f126])).
% 0.20/0.56  fof(f436,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~v1_relat_1(sK3)) ) | (~spl7_1 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f434,f43])).
% 0.20/0.56  fof(f434,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | (~spl7_1 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(resolution,[],[f357,f79])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    r1_partfun1(sK2,sK3) | ~spl7_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f78])).
% 0.20/0.56  fof(f357,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_partfun1(sK2,X0) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f356,f107])).
% 0.20/0.56  fof(f356,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_partfun1(sK2,X0) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) ) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f355,f41])).
% 0.20/0.56  fof(f355,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_partfun1(sK2,X0) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f351,f50])).
% 0.20/0.56  fof(f351,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~r2_hidden(X1,k1_xboole_0) | ~r1_partfun1(sK2,X0) | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.56    inference(superposition,[],[f51,f323])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r1_partfun1(X0,X1) | k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f291,plain,(
% 0.20/0.56    ~spl7_6 | spl7_7),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f290])).
% 0.20/0.56  fof(f290,plain,(
% 0.20/0.56    $false | (~spl7_6 | spl7_7)),
% 0.20/0.56    inference(subsumption_resolution,[],[f277,f50])).
% 0.20/0.56  fof(f277,plain,(
% 0.20/0.56    ~r1_tarski(k1_xboole_0,k1_relat_1(sK2)) | (~spl7_6 | spl7_7)),
% 0.20/0.56    inference(backward_demodulation,[],[f167,f102])).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    ~r1_tarski(sK0,k1_relat_1(sK2)) | spl7_7),
% 0.20/0.56    inference(subsumption_resolution,[],[f166,f147])).
% 0.20/0.56  fof(f147,plain,(
% 0.20/0.56    sK0 != k1_relat_1(sK2) | spl7_7),
% 0.20/0.56    inference(superposition,[],[f112,f106])).
% 0.20/0.56  fof(f112,plain,(
% 0.20/0.56    sK0 != k1_relset_1(sK0,sK1,sK2) | spl7_7),
% 0.20/0.56    inference(avatar_component_clause,[],[f111])).
% 0.20/0.56  fof(f166,plain,(
% 0.20/0.56    sK0 = k1_relat_1(sK2) | ~r1_tarski(sK0,k1_relat_1(sK2))),
% 0.20/0.56    inference(resolution,[],[f158,f57])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(flattening,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.56  fof(f257,plain,(
% 0.20/0.56    spl7_18 | spl7_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f128,f96,f254])).
% 0.20/0.56  fof(f128,plain,(
% 0.20/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.56    inference(subsumption_resolution,[],[f123,f44])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.56    inference(resolution,[],[f45,f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f40])).
% 0.20/0.56  fof(f252,plain,(
% 0.20/0.56    ~spl7_1 | spl7_2 | ~spl7_3 | spl7_5),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f251])).
% 0.20/0.56  fof(f251,plain,(
% 0.20/0.56    $false | (~spl7_1 | spl7_2 | ~spl7_3 | spl7_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f250,f107])).
% 0.20/0.56  fof(f250,plain,(
% 0.20/0.56    ~v1_relat_1(sK2) | (~spl7_1 | spl7_2 | ~spl7_3 | spl7_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f249,f41])).
% 0.20/0.56  fof(f249,plain,(
% 0.20/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_1 | spl7_2 | ~spl7_3 | spl7_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f248,f84])).
% 0.20/0.56  fof(f248,plain,(
% 0.20/0.56    k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_1 | ~spl7_3 | spl7_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f247,f79])).
% 0.20/0.56  fof(f247,plain,(
% 0.20/0.56    ~r1_partfun1(sK2,sK3) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_3 | spl7_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f245,f158])).
% 0.20/0.56  fof(f245,plain,(
% 0.20/0.56    ~r1_tarski(k1_relat_1(sK2),sK0) | ~r1_partfun1(sK2,sK3) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_3 | spl7_5)),
% 0.20/0.56    inference(resolution,[],[f136,f237])).
% 0.20/0.56  fof(f136,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~r1_tarski(k1_relat_1(X0),sK0) | ~r1_partfun1(X0,sK3) | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | spl7_5),
% 0.20/0.56    inference(subsumption_resolution,[],[f135,f126])).
% 0.20/0.56  fof(f135,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),sK0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r1_partfun1(X0,sK3) | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1) | ~v1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | spl7_5),
% 0.20/0.56    inference(subsumption_resolution,[],[f131,f43])).
% 0.20/0.56  fof(f131,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),sK0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r1_partfun1(X0,sK3) | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | spl7_5),
% 0.20/0.56    inference(superposition,[],[f51,f130])).
% 0.20/0.56  fof(f130,plain,(
% 0.20/0.56    sK0 = k1_relat_1(sK3) | spl7_5),
% 0.20/0.56    inference(forward_demodulation,[],[f125,f129])).
% 0.20/0.56  fof(f129,plain,(
% 0.20/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | spl7_5),
% 0.20/0.56    inference(subsumption_resolution,[],[f128,f98])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    k1_xboole_0 != sK1 | spl7_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f96])).
% 0.20/0.56  fof(f236,plain,(
% 0.20/0.56    spl7_1 | spl7_17 | spl7_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f231,f96,f233,f78])).
% 0.20/0.56  fof(f231,plain,(
% 0.20/0.56    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | spl7_5),
% 0.20/0.56    inference(subsumption_resolution,[],[f230,f107])).
% 0.20/0.56  fof(f230,plain,(
% 0.20/0.56    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | ~v1_relat_1(sK2) | spl7_5),
% 0.20/0.56    inference(subsumption_resolution,[],[f209,f41])).
% 0.20/0.56  fof(f209,plain,(
% 0.20/0.56    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_5),
% 0.20/0.56    inference(resolution,[],[f140,f158])).
% 0.20/0.56  fof(f140,plain,(
% 0.20/0.56    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),sK0) | r2_hidden(sK5(X4,sK3),k1_relat_1(X4)) | r1_partfun1(X4,sK3) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | spl7_5),
% 0.20/0.56    inference(subsumption_resolution,[],[f139,f126])).
% 0.20/0.56  fof(f139,plain,(
% 0.20/0.56    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),sK0) | r2_hidden(sK5(X4,sK3),k1_relat_1(X4)) | r1_partfun1(X4,sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | spl7_5),
% 0.20/0.56    inference(subsumption_resolution,[],[f133,f43])).
% 0.20/0.56  fof(f133,plain,(
% 0.20/0.56    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),sK0) | r2_hidden(sK5(X4,sK3),k1_relat_1(X4)) | r1_partfun1(X4,sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | spl7_5),
% 0.20/0.56    inference(superposition,[],[f52,f130])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    ~spl7_5 | spl7_6),
% 0.20/0.56    inference(avatar_split_clause,[],[f46,f100,f96])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f94,plain,(
% 0.20/0.56    spl7_1 | spl7_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f47,f92,f78])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X5] : (k1_funct_1(sK2,X5) = k1_funct_1(sK3,X5) | ~r2_hidden(X5,k1_relset_1(sK0,sK1,sK2)) | r1_partfun1(sK2,sK3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f90,plain,(
% 0.20/0.56    ~spl7_1 | spl7_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f48,f87,f78])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    ~spl7_1 | ~spl7_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f49,f82,f78])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (14684)------------------------------
% 0.20/0.56  % (14684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (14684)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (14684)Memory used [KB]: 11001
% 0.20/0.56  % (14684)Time elapsed: 0.144 s
% 0.20/0.56  % (14684)------------------------------
% 0.20/0.56  % (14684)------------------------------
% 0.20/0.57  % (14675)Success in time 0.201 s
%------------------------------------------------------------------------------
