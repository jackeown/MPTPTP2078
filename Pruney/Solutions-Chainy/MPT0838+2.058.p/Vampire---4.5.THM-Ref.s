%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 441 expanded)
%              Number of leaves         :   30 ( 149 expanded)
%              Depth                    :   17
%              Number of atoms          :  474 (1741 expanded)
%              Number of equality atoms :   48 ( 242 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f437,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f192,f293,f298,f308,f321,f355,f364,f382,f413,f428,f436])).

fof(f436,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl6_4 ),
    inference(resolution,[],[f179,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35,f34,f33])).

% (22837)Refutation not found, incomplete strategy% (22837)------------------------------
% (22837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

% (22837)Termination reason: Refutation not found, incomplete strategy

% (22837)Memory used [KB]: 10746
% (22837)Time elapsed: 0.139 s
% (22837)------------------------------
% (22837)------------------------------
fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

fof(f179,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl6_4
  <=> ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f428,plain,
    ( spl6_4
    | ~ spl6_24
    | spl6_3
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f427,f306,f174,f352,f178])).

fof(f352,plain,
    ( spl6_24
  <=> r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f174,plain,
    ( spl6_3
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f306,plain,
    ( spl6_21
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ r2_hidden(X3,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f427,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl6_3
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f422,f175])).

fof(f175,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f174])).

fof(f422,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_xboole_0(k2_relat_1(sK2)) )
    | spl6_3
    | ~ spl6_21 ),
    inference(superposition,[],[f162,f399])).

fof(f399,plain,
    ( k1_xboole_0 = sK4(k2_relat_1(sK2))
    | spl6_3
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f395,f175])).

fof(f395,plain,
    ( k1_xboole_0 = sK4(k2_relat_1(sK2))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl6_21 ),
    inference(resolution,[],[f307,f75])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f65,f60])).

% (22820)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f60,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f307,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | k1_xboole_0 = X3 )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f306])).

% (22815)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k2_relat_1(X0)),k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(resolution,[],[f161,f52])).

fof(f52,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f161,plain,(
    ! [X6,X4,X5] :
      ( m1_subset_1(sK4(k2_relat_1(X4)),X6)
      | v1_xboole_0(k2_relat_1(X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f159,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k2_relat_1(X0)),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(condensation,[],[f157])).

fof(f157,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | r2_hidden(sK4(k2_relat_1(X0)),X2) ) ),
    inference(resolution,[],[f139,f61])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f139,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_relat_1(X7)
      | v1_xboole_0(k2_relat_1(X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X7))
      | r2_hidden(sK4(k2_relat_1(X4)),X5) ) ),
    inference(resolution,[],[f132,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(k2_relat_1(X0)),X1)
      | v1_xboole_0(k2_relat_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(resolution,[],[f113,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f113,plain,(
    ! [X2,X3] :
      ( ~ v5_relat_1(X2,X3)
      | v1_xboole_0(k2_relat_1(X2))
      | r2_hidden(sK4(k2_relat_1(X2)),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f111,f62])).

% (22821)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(sK4(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f66,f75])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f413,plain,
    ( ~ spl6_21
    | ~ spl6_22
    | spl6_24 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl6_21
    | ~ spl6_22
    | spl6_24 ),
    inference(subsumption_resolution,[],[f405,f354])).

fof(f354,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f352])).

fof(f405,plain,
    ( r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2))
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f315,f393])).

fof(f393,plain,
    ( k1_xboole_0 = sK3(sK2)
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(resolution,[],[f307,f372])).

fof(f372,plain,
    ( r2_hidden(sK3(sK2),k2_relat_1(sK2))
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f371,f50])).

fof(f371,plain,
    ( r2_hidden(sK3(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_22 ),
    inference(superposition,[],[f315,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f315,plain,
    ( r2_hidden(sK3(sK2),k2_relset_1(sK0,sK1,sK2))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl6_22
  <=> r2_hidden(sK3(sK2),k2_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f382,plain,
    ( ~ spl6_6
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl6_6
    | spl6_23 ),
    inference(resolution,[],[f368,f50])).

fof(f368,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl6_6
    | spl6_23 ),
    inference(resolution,[],[f367,f72])).

fof(f367,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ spl6_6
    | spl6_23 ),
    inference(subsumption_resolution,[],[f365,f190])).

fof(f190,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f365,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl6_23 ),
    inference(resolution,[],[f320,f62])).

fof(f320,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl6_23
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f364,plain,
    ( spl6_3
    | ~ spl6_6
    | spl6_22
    | spl6_24 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | spl6_3
    | ~ spl6_6
    | spl6_22
    | spl6_24 ),
    inference(subsumption_resolution,[],[f358,f362])).

fof(f362,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_relat_1(sK2))
    | spl6_24 ),
    inference(subsumption_resolution,[],[f361,f50])).

fof(f361,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_24 ),
    inference(superposition,[],[f354,f70])).

fof(f358,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1(sK2))
    | spl6_3
    | ~ spl6_6
    | spl6_22 ),
    inference(subsumption_resolution,[],[f348,f175])).

fof(f348,plain,
    ( r2_hidden(k1_xboole_0,k2_relat_1(sK2))
    | v1_xboole_0(k2_relat_1(sK2))
    | spl6_3
    | ~ spl6_6
    | spl6_22 ),
    inference(superposition,[],[f75,f342])).

fof(f342,plain,
    ( k1_xboole_0 = sK4(k2_relat_1(sK2))
    | spl6_3
    | ~ spl6_6
    | spl6_22 ),
    inference(subsumption_resolution,[],[f337,f175])).

fof(f337,plain,
    ( k1_xboole_0 = sK4(k2_relat_1(sK2))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl6_6
    | spl6_22 ),
    inference(resolution,[],[f327,f75])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | k1_xboole_0 = X0 )
    | ~ spl6_6
    | spl6_22 ),
    inference(subsumption_resolution,[],[f325,f190])).

fof(f325,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | spl6_22 ),
    inference(resolution,[],[f324,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(X1),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v3_relat_1(X0)
      | r2_hidden(sK3(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ( k1_xboole_0 != sK3(X0)
            & r2_hidden(sK3(X0),k2_relat_1(X0)) ) )
        & ( ! [X2] :
              ( k1_xboole_0 = X2
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & r2_hidden(X1,k2_relat_1(X0)) )
     => ( k1_xboole_0 != sK3(X0)
        & r2_hidden(sK3(X0),k2_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ? [X1] :
              ( k1_xboole_0 != X1
              & r2_hidden(X1,k2_relat_1(X0)) ) )
        & ( ! [X2] :
              ( k1_xboole_0 = X2
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ? [X1] :
              ( k1_xboole_0 != X1
              & r2_hidden(X1,k2_relat_1(X0)) ) )
        & ( ! [X1] :
              ( k1_xboole_0 = X1
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ v3_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0))
      | k1_xboole_0 = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f324,plain,
    ( ~ r2_hidden(sK3(sK2),k2_relat_1(sK2))
    | spl6_22 ),
    inference(subsumption_resolution,[],[f323,f50])).

fof(f323,plain,
    ( ~ r2_hidden(sK3(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_22 ),
    inference(superposition,[],[f316,f70])).

fof(f316,plain,
    ( ~ r2_hidden(sK3(sK2),k2_relset_1(sK0,sK1,sK2))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f314])).

fof(f355,plain,
    ( spl6_4
    | ~ spl6_24
    | spl6_3
    | ~ spl6_6
    | spl6_22 ),
    inference(avatar_split_clause,[],[f350,f314,f189,f174,f352,f178])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl6_3
    | ~ spl6_6
    | spl6_22 ),
    inference(subsumption_resolution,[],[f345,f175])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_xboole_0(k2_relat_1(sK2)) )
    | spl6_3
    | ~ spl6_6
    | spl6_22 ),
    inference(superposition,[],[f162,f342])).

fof(f321,plain,
    ( ~ spl6_22
    | ~ spl6_23
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f311,f303,f318,f314])).

fof(f303,plain,
    ( spl6_20
  <=> ! [X4] :
        ( r2_hidden(sK3(sK2),X4)
        | ~ r1_tarski(k2_relat_1(sK2),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f311,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r2_hidden(sK3(sK2),k2_relset_1(sK0,sK1,sK2))
    | ~ spl6_20 ),
    inference(resolution,[],[f310,f52])).

fof(f310,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(sK2),X2)
        | ~ r1_tarski(k2_relat_1(sK2),X2) )
    | ~ spl6_20 ),
    inference(resolution,[],[f304,f64])).

fof(f304,plain,
    ( ! [X4] :
        ( r2_hidden(sK3(sK2),X4)
        | ~ r1_tarski(k2_relat_1(sK2),X4) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f303])).

fof(f308,plain,
    ( spl6_20
    | spl6_21
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f300,f189,f306,f303])).

fof(f300,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 = X3
        | ~ r2_hidden(X3,k2_relat_1(sK2))
        | r2_hidden(sK3(sK2),X4)
        | ~ r1_tarski(k2_relat_1(sK2),X4) )
    | ~ spl6_6 ),
    inference(resolution,[],[f190,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = X0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | r2_hidden(sK3(X1),X2)
      | ~ r1_tarski(k2_relat_1(X1),X2) ) ),
    inference(resolution,[],[f115,f66])).

fof(f298,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl6_6 ),
    inference(subsumption_resolution,[],[f296,f61])).

fof(f296,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_6 ),
    inference(resolution,[],[f287,f50])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_6 ),
    inference(resolution,[],[f191,f56])).

fof(f191,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f189])).

fof(f293,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f291,f280])).

fof(f280,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(global_subsumption,[],[f50,f123])).

fof(f123,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f51,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f51,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f291,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f285,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f285,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f187,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f187,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f192,plain,
    ( spl6_5
    | ~ spl6_6
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f181,f174,f189,f185])).

fof(f181,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f176,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f176,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (22824)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (22817)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (22825)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (22841)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (22816)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (22818)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (22818)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (22826)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (22840)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (22819)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.53  % (22832)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.54  % (22837)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.54  % (22827)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f437,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(avatar_sat_refutation,[],[f192,f293,f298,f308,f321,f355,f364,f382,f413,f428,f436])).
% 1.27/0.54  fof(f436,plain,(
% 1.27/0.54    ~spl6_4),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f435])).
% 1.27/0.54  fof(f435,plain,(
% 1.27/0.54    $false | ~spl6_4),
% 1.27/0.54    inference(resolution,[],[f179,f50])).
% 1.27/0.54  fof(f50,plain,(
% 1.27/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.27/0.54    inference(cnf_transformation,[],[f36])).
% 1.27/0.54  fof(f36,plain,(
% 1.27/0.54    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35,f34,f33])).
% 1.27/0.54  % (22837)Refutation not found, incomplete strategy% (22837)------------------------------
% 1.27/0.54  % (22837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  fof(f33,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  % (22837)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (22837)Memory used [KB]: 10746
% 1.27/0.54  % (22837)Time elapsed: 0.139 s
% 1.27/0.54  % (22837)------------------------------
% 1.27/0.54  % (22837)------------------------------
% 1.27/0.54  fof(f34,plain,(
% 1.27/0.54    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    ? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.27/0.54    inference(flattening,[],[f17])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f16])).
% 1.27/0.54  fof(f16,negated_conjecture,(
% 1.27/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.27/0.54    inference(negated_conjecture,[],[f15])).
% 1.27/0.54  fof(f15,conjecture,(
% 1.27/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).
% 1.27/0.54  fof(f179,plain,(
% 1.27/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl6_4),
% 1.27/0.54    inference(avatar_component_clause,[],[f178])).
% 1.27/0.54  fof(f178,plain,(
% 1.27/0.54    spl6_4 <=> ! [X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.27/0.54  fof(f428,plain,(
% 1.27/0.54    spl6_4 | ~spl6_24 | spl6_3 | ~spl6_21),
% 1.27/0.54    inference(avatar_split_clause,[],[f427,f306,f174,f352,f178])).
% 1.27/0.54  fof(f352,plain,(
% 1.27/0.54    spl6_24 <=> r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.27/0.54  fof(f174,plain,(
% 1.27/0.54    spl6_3 <=> v1_xboole_0(k2_relat_1(sK2))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.27/0.54  fof(f306,plain,(
% 1.27/0.54    spl6_21 <=> ! [X3] : (k1_xboole_0 = X3 | ~r2_hidden(X3,k2_relat_1(sK2)))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.27/0.54  fof(f427,plain,(
% 1.27/0.54    ( ! [X0] : (~r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (spl6_3 | ~spl6_21)),
% 1.27/0.54    inference(subsumption_resolution,[],[f422,f175])).
% 1.27/0.54  fof(f175,plain,(
% 1.27/0.54    ~v1_xboole_0(k2_relat_1(sK2)) | spl6_3),
% 1.27/0.54    inference(avatar_component_clause,[],[f174])).
% 1.27/0.54  fof(f422,plain,(
% 1.27/0.54    ( ! [X0] : (~r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(k2_relat_1(sK2))) ) | (spl6_3 | ~spl6_21)),
% 1.27/0.54    inference(superposition,[],[f162,f399])).
% 1.27/0.54  fof(f399,plain,(
% 1.27/0.54    k1_xboole_0 = sK4(k2_relat_1(sK2)) | (spl6_3 | ~spl6_21)),
% 1.27/0.54    inference(subsumption_resolution,[],[f395,f175])).
% 1.27/0.54  fof(f395,plain,(
% 1.27/0.54    k1_xboole_0 = sK4(k2_relat_1(sK2)) | v1_xboole_0(k2_relat_1(sK2)) | ~spl6_21),
% 1.27/0.54    inference(resolution,[],[f307,f75])).
% 1.27/0.54  fof(f75,plain,(
% 1.27/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.27/0.54    inference(resolution,[],[f65,f60])).
% 1.27/0.54  % (22820)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.54  fof(f60,plain,(
% 1.27/0.54    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f42])).
% 1.27/0.54  fof(f42,plain,(
% 1.27/0.54    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f41])).
% 1.27/0.54  fof(f41,plain,(
% 1.27/0.54    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f3,axiom,(
% 1.27/0.54    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.27/0.54  fof(f65,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f28])).
% 1.27/0.54  fof(f28,plain,(
% 1.27/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.27/0.54    inference(flattening,[],[f27])).
% 1.27/0.54  fof(f27,plain,(
% 1.27/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f5])).
% 1.27/0.54  fof(f5,axiom,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.27/0.54  fof(f307,plain,(
% 1.27/0.54    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | k1_xboole_0 = X3) ) | ~spl6_21),
% 1.27/0.54    inference(avatar_component_clause,[],[f306])).
% 1.27/0.54  % (22815)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.54  fof(f162,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(k2_relat_1(X0)),k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | v1_xboole_0(k2_relat_1(X0))) )),
% 1.27/0.54    inference(resolution,[],[f161,f52])).
% 1.27/0.54  fof(f52,plain,(
% 1.27/0.54    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f36])).
% 1.27/0.54  fof(f161,plain,(
% 1.27/0.54    ( ! [X6,X4,X5] : (m1_subset_1(sK4(k2_relat_1(X4)),X6) | v1_xboole_0(k2_relat_1(X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 1.27/0.54    inference(resolution,[],[f159,f64])).
% 1.27/0.54  fof(f64,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f26])).
% 1.27/0.54  fof(f26,plain,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f4])).
% 1.27/0.54  fof(f4,axiom,(
% 1.27/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.27/0.54  fof(f159,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(k2_relat_1(X0)),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(k2_relat_1(X0))) )),
% 1.27/0.54    inference(condensation,[],[f157])).
% 1.27/0.54  fof(f157,plain,(
% 1.27/0.54    ( ! [X4,X2,X0,X3,X1] : (v1_xboole_0(k2_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | r2_hidden(sK4(k2_relat_1(X0)),X2)) )),
% 1.27/0.54    inference(resolution,[],[f139,f61])).
% 1.27/0.54  fof(f61,plain,(
% 1.27/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f9])).
% 1.27/0.54  fof(f9,axiom,(
% 1.27/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.27/0.54  fof(f139,plain,(
% 1.27/0.54    ( ! [X6,X4,X7,X5] : (~v1_relat_1(X7) | v1_xboole_0(k2_relat_1(X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | ~m1_subset_1(X4,k1_zfmisc_1(X7)) | r2_hidden(sK4(k2_relat_1(X4)),X5)) )),
% 1.27/0.54    inference(resolution,[],[f132,f56])).
% 1.27/0.54  fof(f56,plain,(
% 1.27/0.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f20])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f6])).
% 1.27/0.54  fof(f6,axiom,(
% 1.27/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.27/0.54  fof(f132,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK4(k2_relat_1(X0)),X1) | v1_xboole_0(k2_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 1.27/0.54    inference(resolution,[],[f113,f72])).
% 1.27/0.54  fof(f72,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f32])).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(ennf_transformation,[],[f12])).
% 1.27/0.54  fof(f12,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.27/0.54  fof(f113,plain,(
% 1.27/0.54    ( ! [X2,X3] : (~v5_relat_1(X2,X3) | v1_xboole_0(k2_relat_1(X2)) | r2_hidden(sK4(k2_relat_1(X2)),X3) | ~v1_relat_1(X2)) )),
% 1.27/0.54    inference(resolution,[],[f111,f62])).
% 1.27/0.54  % (22821)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.54  fof(f62,plain,(
% 1.27/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f43])).
% 1.27/0.54  fof(f43,plain,(
% 1.27/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(nnf_transformation,[],[f25])).
% 1.27/0.54  fof(f25,plain,(
% 1.27/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f7])).
% 1.27/0.54  fof(f7,axiom,(
% 1.27/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.27/0.54  fof(f111,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(sK4(X0),X1) | v1_xboole_0(X0)) )),
% 1.27/0.54    inference(resolution,[],[f66,f75])).
% 1.27/0.54  fof(f66,plain,(
% 1.27/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f47])).
% 1.27/0.54  fof(f47,plain,(
% 1.27/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 1.27/0.54  fof(f46,plain,(
% 1.27/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f45,plain,(
% 1.27/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.27/0.54    inference(rectify,[],[f44])).
% 1.27/0.54  fof(f44,plain,(
% 1.27/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.27/0.54    inference(nnf_transformation,[],[f29])).
% 1.27/0.54  fof(f29,plain,(
% 1.27/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.27/0.54    inference(ennf_transformation,[],[f1])).
% 1.27/0.54  fof(f1,axiom,(
% 1.27/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.27/0.54  fof(f413,plain,(
% 1.27/0.54    ~spl6_21 | ~spl6_22 | spl6_24),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f412])).
% 1.27/0.54  fof(f412,plain,(
% 1.27/0.54    $false | (~spl6_21 | ~spl6_22 | spl6_24)),
% 1.27/0.54    inference(subsumption_resolution,[],[f405,f354])).
% 1.27/0.54  fof(f354,plain,(
% 1.27/0.54    ~r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2)) | spl6_24),
% 1.27/0.54    inference(avatar_component_clause,[],[f352])).
% 1.27/0.54  fof(f405,plain,(
% 1.27/0.54    r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2)) | (~spl6_21 | ~spl6_22)),
% 1.27/0.54    inference(backward_demodulation,[],[f315,f393])).
% 1.27/0.54  fof(f393,plain,(
% 1.27/0.54    k1_xboole_0 = sK3(sK2) | (~spl6_21 | ~spl6_22)),
% 1.27/0.54    inference(resolution,[],[f307,f372])).
% 1.27/0.54  fof(f372,plain,(
% 1.27/0.54    r2_hidden(sK3(sK2),k2_relat_1(sK2)) | ~spl6_22),
% 1.27/0.54    inference(subsumption_resolution,[],[f371,f50])).
% 1.27/0.54  fof(f371,plain,(
% 1.27/0.54    r2_hidden(sK3(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_22),
% 1.27/0.54    inference(superposition,[],[f315,f70])).
% 1.27/0.54  fof(f70,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f31])).
% 1.27/0.54  fof(f31,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(ennf_transformation,[],[f14])).
% 1.27/0.54  fof(f14,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.27/0.54  fof(f315,plain,(
% 1.27/0.54    r2_hidden(sK3(sK2),k2_relset_1(sK0,sK1,sK2)) | ~spl6_22),
% 1.27/0.54    inference(avatar_component_clause,[],[f314])).
% 1.27/0.54  fof(f314,plain,(
% 1.27/0.54    spl6_22 <=> r2_hidden(sK3(sK2),k2_relset_1(sK0,sK1,sK2))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.27/0.54  fof(f382,plain,(
% 1.27/0.54    ~spl6_6 | spl6_23),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f381])).
% 1.27/0.54  fof(f381,plain,(
% 1.27/0.54    $false | (~spl6_6 | spl6_23)),
% 1.27/0.54    inference(resolution,[],[f368,f50])).
% 1.27/0.54  fof(f368,plain,(
% 1.27/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl6_6 | spl6_23)),
% 1.27/0.54    inference(resolution,[],[f367,f72])).
% 1.27/0.54  fof(f367,plain,(
% 1.27/0.54    ~v5_relat_1(sK2,sK1) | (~spl6_6 | spl6_23)),
% 1.27/0.54    inference(subsumption_resolution,[],[f365,f190])).
% 1.27/0.54  fof(f190,plain,(
% 1.27/0.54    v1_relat_1(sK2) | ~spl6_6),
% 1.27/0.54    inference(avatar_component_clause,[],[f189])).
% 1.27/0.54  fof(f189,plain,(
% 1.27/0.54    spl6_6 <=> v1_relat_1(sK2)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.27/0.54  fof(f365,plain,(
% 1.27/0.54    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl6_23),
% 1.27/0.54    inference(resolution,[],[f320,f62])).
% 1.27/0.54  fof(f320,plain,(
% 1.27/0.54    ~r1_tarski(k2_relat_1(sK2),sK1) | spl6_23),
% 1.27/0.54    inference(avatar_component_clause,[],[f318])).
% 1.27/0.54  fof(f318,plain,(
% 1.27/0.54    spl6_23 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.27/0.54  fof(f364,plain,(
% 1.27/0.54    spl6_3 | ~spl6_6 | spl6_22 | spl6_24),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f363])).
% 1.27/0.54  fof(f363,plain,(
% 1.27/0.54    $false | (spl6_3 | ~spl6_6 | spl6_22 | spl6_24)),
% 1.27/0.54    inference(subsumption_resolution,[],[f358,f362])).
% 1.27/0.54  fof(f362,plain,(
% 1.27/0.54    ~r2_hidden(k1_xboole_0,k2_relat_1(sK2)) | spl6_24),
% 1.27/0.54    inference(subsumption_resolution,[],[f361,f50])).
% 1.27/0.54  fof(f361,plain,(
% 1.27/0.54    ~r2_hidden(k1_xboole_0,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_24),
% 1.27/0.54    inference(superposition,[],[f354,f70])).
% 1.27/0.54  fof(f358,plain,(
% 1.27/0.54    r2_hidden(k1_xboole_0,k2_relat_1(sK2)) | (spl6_3 | ~spl6_6 | spl6_22)),
% 1.27/0.54    inference(subsumption_resolution,[],[f348,f175])).
% 1.27/0.54  fof(f348,plain,(
% 1.27/0.54    r2_hidden(k1_xboole_0,k2_relat_1(sK2)) | v1_xboole_0(k2_relat_1(sK2)) | (spl6_3 | ~spl6_6 | spl6_22)),
% 1.27/0.54    inference(superposition,[],[f75,f342])).
% 1.27/0.54  fof(f342,plain,(
% 1.27/0.54    k1_xboole_0 = sK4(k2_relat_1(sK2)) | (spl6_3 | ~spl6_6 | spl6_22)),
% 1.27/0.54    inference(subsumption_resolution,[],[f337,f175])).
% 1.27/0.54  fof(f337,plain,(
% 1.27/0.54    k1_xboole_0 = sK4(k2_relat_1(sK2)) | v1_xboole_0(k2_relat_1(sK2)) | (~spl6_6 | spl6_22)),
% 1.27/0.54    inference(resolution,[],[f327,f75])).
% 1.27/0.54  fof(f327,plain,(
% 1.27/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | k1_xboole_0 = X0) ) | (~spl6_6 | spl6_22)),
% 1.27/0.54    inference(subsumption_resolution,[],[f325,f190])).
% 1.27/0.54  fof(f325,plain,(
% 1.27/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_relat_1(sK2) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | spl6_22),
% 1.27/0.54    inference(resolution,[],[f324,f115])).
% 1.27/0.54  fof(f115,plain,(
% 1.27/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X1),k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 1.27/0.54    inference(duplicate_literal_removal,[],[f114])).
% 1.27/0.54  fof(f114,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1) | r2_hidden(sK3(X1),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.27/0.54    inference(resolution,[],[f53,f54])).
% 1.27/0.54  fof(f54,plain,(
% 1.27/0.54    ( ! [X0] : (v3_relat_1(X0) | r2_hidden(sK3(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f40])).
% 1.27/0.54  fof(f40,plain,(
% 1.27/0.54    ! [X0] : (((v3_relat_1(X0) | (k1_xboole_0 != sK3(X0) & r2_hidden(sK3(X0),k2_relat_1(X0)))) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | ~v3_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 1.27/0.54  fof(f39,plain,(
% 1.27/0.54    ! [X0] : (? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) => (k1_xboole_0 != sK3(X0) & r2_hidden(sK3(X0),k2_relat_1(X0))))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f38,plain,(
% 1.27/0.54    ! [X0] : (((v3_relat_1(X0) | ? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0)))) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | ~v3_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(rectify,[],[f37])).
% 1.27/0.54  fof(f37,plain,(
% 1.27/0.54    ! [X0] : (((v3_relat_1(X0) | ? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0)))) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(nnf_transformation,[],[f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ! [X0] : ((v3_relat_1(X0) <=> ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f11])).
% 1.27/0.54  fof(f11,axiom,(
% 1.27/0.54    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).
% 1.27/0.54  fof(f53,plain,(
% 1.27/0.54    ( ! [X2,X0] : (~v3_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0)) | k1_xboole_0 = X2 | ~v1_relat_1(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f40])).
% 1.27/0.54  fof(f324,plain,(
% 1.27/0.54    ~r2_hidden(sK3(sK2),k2_relat_1(sK2)) | spl6_22),
% 1.27/0.54    inference(subsumption_resolution,[],[f323,f50])).
% 1.27/0.54  fof(f323,plain,(
% 1.27/0.54    ~r2_hidden(sK3(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_22),
% 1.27/0.54    inference(superposition,[],[f316,f70])).
% 1.27/0.54  fof(f316,plain,(
% 1.27/0.54    ~r2_hidden(sK3(sK2),k2_relset_1(sK0,sK1,sK2)) | spl6_22),
% 1.27/0.54    inference(avatar_component_clause,[],[f314])).
% 1.27/0.54  fof(f355,plain,(
% 1.27/0.54    spl6_4 | ~spl6_24 | spl6_3 | ~spl6_6 | spl6_22),
% 1.27/0.54    inference(avatar_split_clause,[],[f350,f314,f189,f174,f352,f178])).
% 1.27/0.54  fof(f350,plain,(
% 1.27/0.54    ( ! [X0] : (~r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (spl6_3 | ~spl6_6 | spl6_22)),
% 1.27/0.54    inference(subsumption_resolution,[],[f345,f175])).
% 1.27/0.54  fof(f345,plain,(
% 1.27/0.54    ( ! [X0] : (~r2_hidden(k1_xboole_0,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(k2_relat_1(sK2))) ) | (spl6_3 | ~spl6_6 | spl6_22)),
% 1.27/0.54    inference(superposition,[],[f162,f342])).
% 1.27/0.54  fof(f321,plain,(
% 1.27/0.54    ~spl6_22 | ~spl6_23 | ~spl6_20),
% 1.27/0.54    inference(avatar_split_clause,[],[f311,f303,f318,f314])).
% 1.27/0.54  fof(f303,plain,(
% 1.27/0.54    spl6_20 <=> ! [X4] : (r2_hidden(sK3(sK2),X4) | ~r1_tarski(k2_relat_1(sK2),X4))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.27/0.54  fof(f311,plain,(
% 1.27/0.54    ~r1_tarski(k2_relat_1(sK2),sK1) | ~r2_hidden(sK3(sK2),k2_relset_1(sK0,sK1,sK2)) | ~spl6_20),
% 1.27/0.54    inference(resolution,[],[f310,f52])).
% 1.27/0.54  fof(f310,plain,(
% 1.27/0.54    ( ! [X2] : (m1_subset_1(sK3(sK2),X2) | ~r1_tarski(k2_relat_1(sK2),X2)) ) | ~spl6_20),
% 1.27/0.54    inference(resolution,[],[f304,f64])).
% 1.27/0.54  fof(f304,plain,(
% 1.27/0.54    ( ! [X4] : (r2_hidden(sK3(sK2),X4) | ~r1_tarski(k2_relat_1(sK2),X4)) ) | ~spl6_20),
% 1.27/0.54    inference(avatar_component_clause,[],[f303])).
% 1.27/0.54  fof(f308,plain,(
% 1.27/0.54    spl6_20 | spl6_21 | ~spl6_6),
% 1.27/0.54    inference(avatar_split_clause,[],[f300,f189,f306,f303])).
% 1.27/0.54  fof(f300,plain,(
% 1.27/0.54    ( ! [X4,X3] : (k1_xboole_0 = X3 | ~r2_hidden(X3,k2_relat_1(sK2)) | r2_hidden(sK3(sK2),X4) | ~r1_tarski(k2_relat_1(sK2),X4)) ) | ~spl6_6),
% 1.27/0.54    inference(resolution,[],[f190,f133])).
% 1.27/0.54  fof(f133,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = X0 | ~r2_hidden(X0,k2_relat_1(X1)) | r2_hidden(sK3(X1),X2) | ~r1_tarski(k2_relat_1(X1),X2)) )),
% 1.27/0.54    inference(resolution,[],[f115,f66])).
% 1.27/0.54  fof(f298,plain,(
% 1.27/0.54    spl6_6),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f297])).
% 1.27/0.54  fof(f297,plain,(
% 1.27/0.54    $false | spl6_6),
% 1.27/0.54    inference(subsumption_resolution,[],[f296,f61])).
% 1.27/0.54  fof(f296,plain,(
% 1.27/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_6),
% 1.27/0.54    inference(resolution,[],[f287,f50])).
% 1.27/0.54  fof(f287,plain,(
% 1.27/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_6),
% 1.27/0.54    inference(resolution,[],[f191,f56])).
% 1.27/0.54  fof(f191,plain,(
% 1.27/0.54    ~v1_relat_1(sK2) | spl6_6),
% 1.27/0.54    inference(avatar_component_clause,[],[f189])).
% 1.27/0.54  fof(f293,plain,(
% 1.27/0.54    ~spl6_5),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f292])).
% 1.27/0.54  fof(f292,plain,(
% 1.27/0.54    $false | ~spl6_5),
% 1.27/0.54    inference(subsumption_resolution,[],[f291,f280])).
% 1.27/0.54  fof(f280,plain,(
% 1.27/0.54    k1_xboole_0 != k1_relat_1(sK2)),
% 1.27/0.54    inference(global_subsumption,[],[f50,f123])).
% 1.27/0.54  fof(f123,plain,(
% 1.27/0.54    k1_xboole_0 != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.27/0.54    inference(superposition,[],[f51,f69])).
% 1.27/0.54  fof(f69,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f30])).
% 1.27/0.54  fof(f30,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(ennf_transformation,[],[f13])).
% 1.27/0.54  fof(f13,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.27/0.54  fof(f51,plain,(
% 1.27/0.54    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 1.27/0.54    inference(cnf_transformation,[],[f36])).
% 1.27/0.54  fof(f291,plain,(
% 1.27/0.54    k1_xboole_0 = k1_relat_1(sK2) | ~spl6_5),
% 1.27/0.54    inference(resolution,[],[f285,f57])).
% 1.27/0.54  fof(f57,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f21])).
% 1.27/0.54  fof(f21,plain,(
% 1.27/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.27/0.54  fof(f285,plain,(
% 1.27/0.54    v1_xboole_0(k1_relat_1(sK2)) | ~spl6_5),
% 1.27/0.54    inference(resolution,[],[f187,f58])).
% 1.27/0.54  fof(f58,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f22])).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f8])).
% 1.27/0.54  fof(f8,axiom,(
% 1.27/0.54    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.27/0.54  fof(f187,plain,(
% 1.27/0.54    v1_xboole_0(sK2) | ~spl6_5),
% 1.27/0.54    inference(avatar_component_clause,[],[f185])).
% 1.27/0.54  fof(f185,plain,(
% 1.27/0.54    spl6_5 <=> v1_xboole_0(sK2)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.27/0.54  fof(f192,plain,(
% 1.27/0.54    spl6_5 | ~spl6_6 | ~spl6_3),
% 1.27/0.54    inference(avatar_split_clause,[],[f181,f174,f189,f185])).
% 1.27/0.54  fof(f181,plain,(
% 1.27/0.54    ~v1_relat_1(sK2) | v1_xboole_0(sK2) | ~spl6_3),
% 1.27/0.54    inference(resolution,[],[f176,f59])).
% 1.27/0.54  fof(f59,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f24])).
% 1.27/0.54  fof(f24,plain,(
% 1.27/0.54    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.27/0.54    inference(flattening,[],[f23])).
% 1.27/0.54  fof(f23,plain,(
% 1.27/0.54    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.27/0.54    inference(ennf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,axiom,(
% 1.27/0.54    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 1.27/0.54  fof(f176,plain,(
% 1.27/0.54    v1_xboole_0(k2_relat_1(sK2)) | ~spl6_3),
% 1.27/0.54    inference(avatar_component_clause,[],[f174])).
% 1.27/0.54  % SZS output end Proof for theBenchmark
% 1.27/0.54  % (22818)------------------------------
% 1.27/0.54  % (22818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (22818)Termination reason: Refutation
% 1.27/0.54  
% 1.27/0.54  % (22818)Memory used [KB]: 11001
% 1.27/0.54  % (22818)Time elapsed: 0.099 s
% 1.27/0.54  % (22818)------------------------------
% 1.27/0.54  % (22818)------------------------------
% 1.27/0.54  % (22811)Success in time 0.174 s
%------------------------------------------------------------------------------
