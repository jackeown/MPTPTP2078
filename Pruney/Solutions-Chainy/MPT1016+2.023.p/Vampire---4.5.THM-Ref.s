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
% DateTime   : Thu Dec  3 13:05:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 423 expanded)
%              Number of leaves         :   37 ( 150 expanded)
%              Depth                    :   17
%              Number of atoms          :  629 (2665 expanded)
%              Number of equality atoms :  129 ( 723 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f97,f108,f117,f121,f123,f145,f169,f171,f180,f185,f190,f202,f259,f277,f281,f310,f317,f320,f353])).

fof(f353,plain,
    ( ~ spl7_5
    | ~ spl7_23
    | ~ spl7_35
    | spl7_38 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_23
    | ~ spl7_35
    | spl7_38 ),
    inference(subsumption_resolution,[],[f263,f324])).

fof(f324,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_35
    | spl7_38 ),
    inference(backward_demodulation,[],[f316,f296])).

fof(f296,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl7_35
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f316,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | spl7_38 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl7_38
  <=> r2_hidden(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f263,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f91,f201])).

% (11824)Refutation not found, incomplete strategy% (11824)------------------------------
% (11824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11841)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (11823)Refutation not found, incomplete strategy% (11823)------------------------------
% (11823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f201,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl7_23
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f91,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_5
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f320,plain,(
    spl7_34 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | spl7_34 ),
    inference(resolution,[],[f293,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f293,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK1))
    | spl7_34 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl7_34
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f317,plain,
    ( spl7_2
    | ~ spl7_38
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f313,f217,f315,f78])).

fof(f78,plain,
    ( spl7_2
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f217,plain,
    ( spl7_26
  <=> ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | sK3 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f313,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | sK2 = sK3
    | ~ spl7_26 ),
    inference(equality_resolution,[],[f218])).

fof(f218,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | sK3 = X2 )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f217])).

fof(f310,plain,
    ( spl7_35
    | ~ spl7_34
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f309,f200,f292,f295])).

fof(f309,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK1))
    | k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f308,f201])).

fof(f308,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f181,f201])).

fof(f181,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f147,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f147,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f133,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f133,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(global_subsumption,[],[f45,f132])).

fof(f132,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f70,f110])).

fof(f110,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f45,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ( sK2 != sK3
        & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK0)
        & r2_hidden(sK2,sK0) )
      | ~ v2_funct_1(sK1) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
          | ~ r2_hidden(X5,sK0)
          | ~ r2_hidden(X4,sK0) )
      | v2_funct_1(sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK0)
            & r2_hidden(X2,sK0) )
        | ~ v2_funct_1(sK1) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
            | ~ r2_hidden(X5,sK0)
            | ~ r2_hidden(X4,sK0) )
        | v2_funct_1(sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f281,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | ~ spl7_1
    | ~ spl7_25
    | spl7_26
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f279,f82,f217,f214,f75,f103,f100])).

fof(f100,plain,
    ( spl7_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f103,plain,
    ( spl7_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f75,plain,
    ( spl7_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f214,plain,
    ( spl7_25
  <=> r2_hidden(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f82,plain,
    ( spl7_3
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f279,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X1)
        | sK3 = X1
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_3 ),
    inference(superposition,[],[f53,f83])).

fof(f83,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f53,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f277,plain,
    ( ~ spl7_4
    | ~ spl7_23
    | spl7_25 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_23
    | spl7_25 ),
    inference(subsumption_resolution,[],[f262,f232])).

fof(f232,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | spl7_25 ),
    inference(resolution,[],[f221,f51])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | ~ r2_hidden(sK3,X0) )
    | spl7_25 ),
    inference(resolution,[],[f215,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f215,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK1))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f214])).

fof(f262,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f87,f201])).

fof(f87,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl7_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f259,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f79,f254])).

fof(f254,plain,
    ( sK2 = sK3
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f226,f223])).

fof(f223,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(resolution,[],[f198,f91])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl7_22
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f226,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f222,f83])).

fof(f222,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(resolution,[],[f198,f87])).

fof(f79,plain,
    ( sK2 != sK3
    | spl7_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f202,plain,
    ( ~ spl7_1
    | spl7_22
    | spl7_23 ),
    inference(avatar_split_clause,[],[f195,f200,f197,f75])).

fof(f195,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(global_subsumption,[],[f44,f43,f109])).

fof(f109,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f45,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f190,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_1
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f189,f178,f75,f103,f100])).

fof(f178,plain,
    ( spl7_21
  <=> sK4(sK1) = sK5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f189,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_21 ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_21 ),
    inference(superposition,[],[f57,f179])).

fof(f179,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f178])).

fof(f57,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f185,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_1
    | ~ spl7_19
    | spl7_20 ),
    inference(avatar_split_clause,[],[f183,f175,f167,f75,f103,f100])).

fof(f167,plain,
    ( spl7_19
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f175,plain,
    ( spl7_20
  <=> r2_hidden(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f183,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_20 ),
    inference(resolution,[],[f182,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1),X0)
        | ~ r1_tarski(X0,sK0) )
    | spl7_20 ),
    inference(resolution,[],[f176,f64])).

fof(f176,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f180,plain,
    ( ~ spl7_20
    | spl7_21
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f173,f142,f178,f175])).

fof(f142,plain,
    ( spl7_14
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f173,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ r2_hidden(sK4(sK1),sK0)
    | ~ spl7_14 ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f171,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl7_19 ),
    inference(subsumption_resolution,[],[f147,f168])).

fof(f168,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f169,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_1
    | ~ spl7_19
    | spl7_13 ),
    inference(avatar_split_clause,[],[f164,f139,f167,f75,f103,f100])).

fof(f139,plain,
    ( spl7_13
  <=> r2_hidden(sK5(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f164,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_13 ),
    inference(resolution,[],[f146,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1),X0)
        | ~ r1_tarski(X0,sK0) )
    | spl7_13 ),
    inference(resolution,[],[f140,f64])).

fof(f140,plain,
    ( ~ r2_hidden(sK5(sK1),sK0)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f145,plain,
    ( ~ spl7_13
    | spl7_14
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f135,f106,f95,f142,f139])).

fof(f95,plain,
    ( spl7_6
  <=> ! [X5,X4] :
        ( X4 = X5
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f106,plain,
    ( spl7_9
  <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f135,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1))
        | ~ r2_hidden(sK5(sK1),sK0)
        | ~ r2_hidden(X1,sK0)
        | sK5(sK1) = X1 )
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(superposition,[],[f96,f107])).

fof(f107,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f96,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X5,sK0)
        | X4 = X5 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f123,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f43,f104])).

fof(f104,plain,
    ( ~ v1_funct_1(sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f121,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl7_10 ),
    inference(resolution,[],[f115,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f115,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_10
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f117,plain,
    ( ~ spl7_10
    | spl7_7 ),
    inference(avatar_split_clause,[],[f112,f100,f114])).

fof(f112,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f108,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | spl7_1 ),
    inference(avatar_split_clause,[],[f98,f75,f106,f103,f100])).

fof(f98,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_1 ),
    inference(resolution,[],[f76,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,
    ( ~ v2_funct_1(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f97,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f46,f95,f75])).

fof(f46,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f47,f90,f75])).

fof(f47,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f48,f86,f75])).

fof(f48,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f49,f82,f75])).

fof(f49,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f50,f78,f75])).

fof(f50,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:23:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (11815)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (11821)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (11817)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (11830)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (11818)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (11838)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (11832)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (11820)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (11816)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (11813)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (11815)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (11828)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (11824)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (11833)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (11842)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (11822)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (11814)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (11843)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (11819)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (11823)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f354,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f97,f108,f117,f121,f123,f145,f169,f171,f180,f185,f190,f202,f259,f277,f281,f310,f317,f320,f353])).
% 0.22/0.54  fof(f353,plain,(
% 0.22/0.54    ~spl7_5 | ~spl7_23 | ~spl7_35 | spl7_38),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f351])).
% 0.22/0.54  fof(f351,plain,(
% 0.22/0.54    $false | (~spl7_5 | ~spl7_23 | ~spl7_35 | spl7_38)),
% 0.22/0.54    inference(subsumption_resolution,[],[f263,f324])).
% 0.22/0.54  fof(f324,plain,(
% 0.22/0.54    ~r2_hidden(sK2,k1_xboole_0) | (~spl7_35 | spl7_38)),
% 0.22/0.54    inference(backward_demodulation,[],[f316,f296])).
% 0.22/0.54  fof(f296,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(sK1) | ~spl7_35),
% 0.22/0.54    inference(avatar_component_clause,[],[f295])).
% 0.22/0.54  fof(f295,plain,(
% 0.22/0.54    spl7_35 <=> k1_xboole_0 = k1_relat_1(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.22/0.54  fof(f316,plain,(
% 0.22/0.54    ~r2_hidden(sK2,k1_relat_1(sK1)) | spl7_38),
% 0.22/0.54    inference(avatar_component_clause,[],[f315])).
% 0.22/0.54  fof(f315,plain,(
% 0.22/0.54    spl7_38 <=> r2_hidden(sK2,k1_relat_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    r2_hidden(sK2,k1_xboole_0) | (~spl7_5 | ~spl7_23)),
% 0.22/0.54    inference(backward_demodulation,[],[f91,f201])).
% 0.22/0.54  % (11824)Refutation not found, incomplete strategy% (11824)------------------------------
% 0.22/0.54  % (11824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11841)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (11823)Refutation not found, incomplete strategy% (11823)------------------------------
% 0.22/0.54  % (11823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  fof(f201,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | ~spl7_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f200])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    spl7_23 <=> k1_xboole_0 = sK0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    r2_hidden(sK2,sK0) | ~spl7_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    spl7_5 <=> r2_hidden(sK2,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.54  fof(f320,plain,(
% 0.22/0.54    spl7_34),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f319])).
% 0.22/0.54  fof(f319,plain,(
% 0.22/0.54    $false | spl7_34),
% 0.22/0.54    inference(resolution,[],[f293,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,k1_relat_1(sK1)) | spl7_34),
% 0.22/0.54    inference(avatar_component_clause,[],[f292])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    spl7_34 <=> r1_tarski(k1_xboole_0,k1_relat_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.22/0.54  fof(f317,plain,(
% 0.22/0.54    spl7_2 | ~spl7_38 | ~spl7_26),
% 0.22/0.54    inference(avatar_split_clause,[],[f313,f217,f315,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    spl7_2 <=> sK2 = sK3),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    spl7_26 <=> ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | ~r2_hidden(X2,k1_relat_1(sK1)) | sK3 = X2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.54  fof(f313,plain,(
% 0.22/0.54    ~r2_hidden(sK2,k1_relat_1(sK1)) | sK2 = sK3 | ~spl7_26),
% 0.22/0.54    inference(equality_resolution,[],[f218])).
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    ( ! [X2] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,sK2) | ~r2_hidden(X2,k1_relat_1(sK1)) | sK3 = X2) ) | ~spl7_26),
% 0.22/0.54    inference(avatar_component_clause,[],[f217])).
% 0.22/0.54  fof(f310,plain,(
% 0.22/0.54    spl7_35 | ~spl7_34 | ~spl7_23),
% 0.22/0.54    inference(avatar_split_clause,[],[f309,f200,f292,f295])).
% 0.22/0.54  fof(f309,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,k1_relat_1(sK1)) | k1_xboole_0 = k1_relat_1(sK1) | ~spl7_23),
% 0.22/0.54    inference(forward_demodulation,[],[f308,f201])).
% 0.22/0.54  fof(f308,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(sK1) | ~r1_tarski(sK0,k1_relat_1(sK1)) | ~spl7_23),
% 0.22/0.54    inference(forward_demodulation,[],[f181,f201])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK1) | ~r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.54    inference(resolution,[],[f147,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.22/0.54    inference(resolution,[],[f133,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(global_subsumption,[],[f45,f132])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.54    inference(superposition,[],[f70,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.22/0.54    inference(resolution,[],[f45,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f30,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.54    inference(rectify,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.54    inference(negated_conjecture,[],[f12])).
% 0.22/0.54  fof(f12,conjecture,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.22/0.54  fof(f281,plain,(
% 0.22/0.54    ~spl7_7 | ~spl7_8 | ~spl7_1 | ~spl7_25 | spl7_26 | ~spl7_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f279,f82,f217,f214,f75,f103,f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    spl7_7 <=> v1_relat_1(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    spl7_8 <=> v1_funct_1(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    spl7_1 <=> v2_funct_1(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.54  fof(f214,plain,(
% 0.22/0.54    spl7_25 <=> r2_hidden(sK3,k1_relat_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    spl7_3 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.55  fof(f279,plain,(
% 0.22/0.55    ( ! [X1] : (k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X1) | sK3 = X1 | ~r2_hidden(X1,k1_relat_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl7_3),
% 0.22/0.55    inference(superposition,[],[f53,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl7_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f82])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(rectify,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.22/0.55  fof(f277,plain,(
% 0.22/0.55    ~spl7_4 | ~spl7_23 | spl7_25),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f275])).
% 0.22/0.55  fof(f275,plain,(
% 0.22/0.55    $false | (~spl7_4 | ~spl7_23 | spl7_25)),
% 0.22/0.55    inference(subsumption_resolution,[],[f262,f232])).
% 0.22/0.55  fof(f232,plain,(
% 0.22/0.55    ~r2_hidden(sK3,k1_xboole_0) | spl7_25),
% 0.22/0.55    inference(resolution,[],[f221,f51])).
% 0.22/0.55  fof(f221,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | ~r2_hidden(sK3,X0)) ) | spl7_25),
% 0.22/0.55    inference(resolution,[],[f215,f64])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f215,plain,(
% 0.22/0.55    ~r2_hidden(sK3,k1_relat_1(sK1)) | spl7_25),
% 0.22/0.55    inference(avatar_component_clause,[],[f214])).
% 0.22/0.55  fof(f262,plain,(
% 0.22/0.55    r2_hidden(sK3,k1_xboole_0) | (~spl7_4 | ~spl7_23)),
% 0.22/0.55    inference(backward_demodulation,[],[f87,f201])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    r2_hidden(sK3,sK0) | ~spl7_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f86])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    spl7_4 <=> r2_hidden(sK3,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.55  fof(f259,plain,(
% 0.22/0.55    spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_22),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f255])).
% 0.22/0.55  fof(f255,plain,(
% 0.22/0.55    $false | (spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_22)),
% 0.22/0.55    inference(subsumption_resolution,[],[f79,f254])).
% 0.22/0.55  fof(f254,plain,(
% 0.22/0.55    sK2 = sK3 | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_22)),
% 0.22/0.55    inference(forward_demodulation,[],[f226,f223])).
% 0.22/0.55  fof(f223,plain,(
% 0.22/0.55    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_5 | ~spl7_22)),
% 0.22/0.55    inference(resolution,[],[f198,f91])).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl7_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f197])).
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    spl7_22 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.55  fof(f226,plain,(
% 0.22/0.55    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_3 | ~spl7_4 | ~spl7_22)),
% 0.22/0.55    inference(forward_demodulation,[],[f222,f83])).
% 0.22/0.55  fof(f222,plain,(
% 0.22/0.55    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl7_4 | ~spl7_22)),
% 0.22/0.55    inference(resolution,[],[f198,f87])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    sK2 != sK3 | spl7_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f78])).
% 0.22/0.55  fof(f202,plain,(
% 0.22/0.55    ~spl7_1 | spl7_22 | spl7_23),
% 0.22/0.55    inference(avatar_split_clause,[],[f195,f200,f197,f75])).
% 0.22/0.55  fof(f195,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.22/0.55    inference(global_subsumption,[],[f44,f43,f109])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 0.22/0.55    inference(resolution,[],[f45,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    v1_funct_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f190,plain,(
% 0.22/0.55    ~spl7_7 | ~spl7_8 | spl7_1 | ~spl7_21),
% 0.22/0.55    inference(avatar_split_clause,[],[f189,f178,f75,f103,f100])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    spl7_21 <=> sK4(sK1) = sK5(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_21),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f188])).
% 0.22/0.55  fof(f188,plain,(
% 0.22/0.55    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_21),
% 0.22/0.55    inference(superposition,[],[f57,f179])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    sK4(sK1) = sK5(sK1) | ~spl7_21),
% 0.22/0.55    inference(avatar_component_clause,[],[f178])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X0] : (sK4(X0) != sK5(X0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f185,plain,(
% 0.22/0.55    ~spl7_7 | ~spl7_8 | spl7_1 | ~spl7_19 | spl7_20),
% 0.22/0.55    inference(avatar_split_clause,[],[f183,f175,f167,f75,f103,f100])).
% 0.22/0.55  fof(f167,plain,(
% 0.22/0.55    spl7_19 <=> r1_tarski(k1_relat_1(sK1),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    spl7_20 <=> r2_hidden(sK4(sK1),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_20),
% 0.22/0.55    inference(resolution,[],[f182,f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f182,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(sK4(sK1),X0) | ~r1_tarski(X0,sK0)) ) | spl7_20),
% 0.22/0.55    inference(resolution,[],[f176,f64])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    ~r2_hidden(sK4(sK1),sK0) | spl7_20),
% 0.22/0.55    inference(avatar_component_clause,[],[f175])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    ~spl7_20 | spl7_21 | ~spl7_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f173,f142,f178,f175])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    spl7_14 <=> ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    sK4(sK1) = sK5(sK1) | ~r2_hidden(sK4(sK1),sK0) | ~spl7_14),
% 0.22/0.55    inference(equality_resolution,[],[f143])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0)) ) | ~spl7_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f142])).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    spl7_19),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    $false | spl7_19),
% 0.22/0.55    inference(subsumption_resolution,[],[f147,f168])).
% 0.22/0.55  fof(f168,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(sK1),sK0) | spl7_19),
% 0.22/0.55    inference(avatar_component_clause,[],[f167])).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    ~spl7_7 | ~spl7_8 | spl7_1 | ~spl7_19 | spl7_13),
% 0.22/0.55    inference(avatar_split_clause,[],[f164,f139,f167,f75,f103,f100])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    spl7_13 <=> r2_hidden(sK5(sK1),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.55  fof(f164,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(sK1),sK0) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_13),
% 0.22/0.55    inference(resolution,[],[f146,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(sK5(sK1),X0) | ~r1_tarski(X0,sK0)) ) | spl7_13),
% 0.22/0.55    inference(resolution,[],[f140,f64])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    ~r2_hidden(sK5(sK1),sK0) | spl7_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f139])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    ~spl7_13 | spl7_14 | ~spl7_6 | ~spl7_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f135,f106,f95,f142,f139])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    spl7_6 <=> ! [X5,X4] : (X4 = X5 | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    spl7_9 <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ( ! [X1] : (k1_funct_1(sK1,X1) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(sK5(sK1),sK0) | ~r2_hidden(X1,sK0) | sK5(sK1) = X1) ) | (~spl7_6 | ~spl7_9)),
% 0.22/0.55    inference(superposition,[],[f96,f107])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~spl7_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f106])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ( ! [X4,X5] : (k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X4,sK0) | ~r2_hidden(X5,sK0) | X4 = X5) ) | ~spl7_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f95])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    spl7_8),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f122])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    $false | spl7_8),
% 0.22/0.55    inference(subsumption_resolution,[],[f43,f104])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    ~v1_funct_1(sK1) | spl7_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f103])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    spl7_10),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    $false | spl7_10),
% 0.22/0.55    inference(resolution,[],[f115,f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl7_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f114])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    spl7_10 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    ~spl7_10 | spl7_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f112,f100,f114])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.22/0.55    inference(resolution,[],[f45,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    ~spl7_7 | ~spl7_8 | spl7_9 | spl7_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f98,f75,f106,f103,f100])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_1),
% 0.22/0.55    inference(resolution,[],[f76,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ~v2_funct_1(sK1) | spl7_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f75])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    spl7_1 | spl7_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f46,f95,f75])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ~spl7_1 | spl7_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f47,f90,f75])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ~spl7_1 | spl7_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f48,f86,f75])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ~spl7_1 | spl7_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f49,f82,f75])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ~spl7_1 | ~spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f50,f78,f75])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (11815)------------------------------
% 0.22/0.55  % (11815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11815)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (11815)Memory used [KB]: 10874
% 0.22/0.55  % (11815)Time elapsed: 0.122 s
% 0.22/0.55  % (11815)------------------------------
% 0.22/0.55  % (11815)------------------------------
% 0.22/0.55  % (11837)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (11836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (11823)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11823)Memory used [KB]: 10746
% 0.22/0.55  % (11823)Time elapsed: 0.140 s
% 0.22/0.55  % (11823)------------------------------
% 0.22/0.55  % (11823)------------------------------
% 0.22/0.55  % (11831)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (11812)Success in time 0.183 s
%------------------------------------------------------------------------------
