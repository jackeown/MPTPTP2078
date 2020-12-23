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
% DateTime   : Thu Dec  3 13:08:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 112 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  259 ( 467 expanded)
%              Number of equality atoms :   34 (  60 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f126,f138,f141])).

fof(f141,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f43,f125,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f125,plain,
    ( v1_xboole_0(k1_tarski(sK2))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_9
  <=> v1_xboole_0(k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f43,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

% (27005)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f138,plain,
    ( spl7_9
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f135,f119,f63,f58,f53,f48,f123])).

fof(f48,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f53,plain,
    ( spl7_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f58,plain,
    ( spl7_3
  <=> m1_funct_2(k1_tarski(sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f63,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f119,plain,
    ( spl7_8
  <=> sK2 = sK5(sK0,sK1,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f135,plain,
    ( v1_xboole_0(k1_tarski(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f134,f60])).

fof(f60,plain,
    ( ~ m1_funct_2(k1_tarski(sK2),sK0,sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f134,plain,
    ( m1_funct_2(k1_tarski(sK2),sK0,sK1)
    | v1_xboole_0(k1_tarski(sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f133,f55])).

fof(f55,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f133,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | m1_funct_2(k1_tarski(sK2),sK0,sK1)
    | v1_xboole_0(k1_tarski(sK2))
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f132,f65])).

fof(f65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f132,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | m1_funct_2(k1_tarski(sK2),sK0,sK1)
    | v1_xboole_0(k1_tarski(sK2))
    | ~ spl7_1
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f130,f50])).

fof(f50,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f130,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | m1_funct_2(k1_tarski(sK2),sK0,sK1)
    | v1_xboole_0(k1_tarski(sK2))
    | ~ spl7_8 ),
    inference(superposition,[],[f41,f121])).

fof(f121,plain,
    ( sK2 = sK5(sK0,sK1,k1_tarski(sK2))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK5(X0,X1,X2))
      | ~ m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK5(X0,X1,X2),X0,X1)
      | m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ( ( ~ m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(sK5(X0,X1,X2),X0,X1)
              | ~ v1_funct_1(sK5(X0,X1,X2)) )
            & m1_subset_1(sK5(X0,X1,X2),X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,X2) )
     => ( ( ~ m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(sK5(X0,X1,X2),X0,X1)
          | ~ v1_funct_1(sK5(X0,X1,X2)) )
        & m1_subset_1(sK5(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
              | ~ m1_subset_1(X3,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).

fof(f126,plain,
    ( spl7_8
    | spl7_9
    | spl7_3 ),
    inference(avatar_split_clause,[],[f100,f58,f123,f119])).

fof(f100,plain,
    ( v1_xboole_0(k1_tarski(sK2))
    | sK2 = sK5(sK0,sK1,k1_tarski(sK2))
    | spl7_3 ),
    inference(resolution,[],[f94,f60])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(k1_tarski(X0),X1,X2)
      | v1_xboole_0(k1_tarski(X0))
      | sK5(X1,X2,k1_tarski(X0)) = X0 ) ),
    inference(resolution,[],[f73,f44])).

fof(f44,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X1,X2,X0),X0)
      | v1_xboole_0(X0)
      | m1_funct_2(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X0,X1,X2)
      | v1_xboole_0(X0)
      | v1_xboole_0(X0)
      | r2_hidden(sK5(X1,X2,X0),X0) ) ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),X2)
      | m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ m1_funct_2(k1_tarski(sK2),sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ m1_funct_2(k1_tarski(sK2),sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_funct_2(k1_tarski(X2),X0,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => m1_funct_2(k1_tarski(X2),X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => m1_funct_2(k1_tarski(X2),X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_funct_2)).

fof(f61,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    ~ m1_funct_2(k1_tarski(sK2),sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f26,f48])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (26987)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (26996)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (27007)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (27008)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (26997)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (26987)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (26988)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.55  % (26993)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (27003)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f126,f138,f141])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    ~spl7_9),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    $false | ~spl7_9),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f43,f125,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.55    inference(rectify,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    v1_xboole_0(k1_tarski(sK2)) | ~spl7_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f123])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    spl7_9 <=> v1_xboole_0(k1_tarski(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.55    inference(equality_resolution,[],[f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.55    inference(equality_resolution,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.21/0.55  % (27005)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.55    inference(rectify,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    spl7_9 | ~spl7_1 | ~spl7_2 | spl7_3 | ~spl7_4 | ~spl7_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f135,f119,f63,f58,f53,f48,f123])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    spl7_1 <=> v1_funct_1(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    spl7_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    spl7_3 <=> m1_funct_2(k1_tarski(sK2),sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    spl7_8 <=> sK2 = sK5(sK0,sK1,k1_tarski(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    v1_xboole_0(k1_tarski(sK2)) | (~spl7_1 | ~spl7_2 | spl7_3 | ~spl7_4 | ~spl7_8)),
% 0.21/0.55    inference(subsumption_resolution,[],[f134,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ~m1_funct_2(k1_tarski(sK2),sK0,sK1) | spl7_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f58])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    m1_funct_2(k1_tarski(sK2),sK0,sK1) | v1_xboole_0(k1_tarski(sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_8)),
% 0.21/0.55    inference(subsumption_resolution,[],[f133,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    v1_funct_2(sK2,sK0,sK1) | ~spl7_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f53])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ~v1_funct_2(sK2,sK0,sK1) | m1_funct_2(k1_tarski(sK2),sK0,sK1) | v1_xboole_0(k1_tarski(sK2)) | (~spl7_1 | ~spl7_4 | ~spl7_8)),
% 0.21/0.55    inference(subsumption_resolution,[],[f132,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f63])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | m1_funct_2(k1_tarski(sK2),sK0,sK1) | v1_xboole_0(k1_tarski(sK2)) | (~spl7_1 | ~spl7_8)),
% 0.21/0.55    inference(subsumption_resolution,[],[f130,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    v1_funct_1(sK2) | ~spl7_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f48])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | m1_funct_2(k1_tarski(sK2),sK0,sK1) | v1_xboole_0(k1_tarski(sK2)) | ~spl7_8),
% 0.21/0.55    inference(superposition,[],[f41,f121])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    sK2 = sK5(sK0,sK1,k1_tarski(sK2)) | ~spl7_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f119])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(sK5(X0,X1,X2)) | ~m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK5(X0,X1,X2),X0,X1) | m1_funct_2(X2,X0,X1) | v1_xboole_0(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ((~m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK5(X0,X1,X2),X0,X1) | ~v1_funct_1(sK5(X0,X1,X2))) & m1_subset_1(sK5(X0,X1,X2),X2))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) | ~m1_subset_1(X4,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2)) => ((~m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK5(X0,X1,X2),X0,X1) | ~v1_funct_1(sK5(X0,X1,X2))) & m1_subset_1(sK5(X0,X1,X2),X2)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) | ~m1_subset_1(X4,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.21/0.55    inference(rectify,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2))) & (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~m1_subset_1(X3,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_funct_2(X2,X0,X1) <=> ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~m1_subset_1(X3,X2))) | v1_xboole_0(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) => (m1_funct_2(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,X2) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    spl7_8 | spl7_9 | spl7_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f100,f58,f123,f119])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    v1_xboole_0(k1_tarski(sK2)) | sK2 = sK5(sK0,sK1,k1_tarski(sK2)) | spl7_3),
% 0.21/0.55    inference(resolution,[],[f94,f60])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_funct_2(k1_tarski(X0),X1,X2) | v1_xboole_0(k1_tarski(X0)) | sK5(X1,X2,k1_tarski(X0)) = X0) )),
% 0.21/0.55    inference(resolution,[],[f73,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.55    inference(equality_resolution,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK5(X1,X2,X0),X0) | v1_xboole_0(X0) | m1_funct_2(X0,X1,X2)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_funct_2(X0,X1,X2) | v1_xboole_0(X0) | v1_xboole_0(X0) | r2_hidden(sK5(X1,X2,X0),X0)) )),
% 0.21/0.55    inference(resolution,[],[f40,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),X2) | m1_funct_2(X2,X0,X1) | v1_xboole_0(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    spl7_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f28,f63])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ~m1_funct_2(k1_tarski(sK2),sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (~m1_funct_2(k1_tarski(X2),X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~m1_funct_2(k1_tarski(sK2),sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (~m1_funct_2(k1_tarski(X2),X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f7])).
% 0.21/0.55  fof(f7,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (~m1_funct_2(k1_tarski(X2),X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => m1_funct_2(k1_tarski(X2),X0,X1))),
% 0.21/0.55    inference(negated_conjecture,[],[f5])).
% 0.21/0.55  fof(f5,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => m1_funct_2(k1_tarski(X2),X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_funct_2)).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ~spl7_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f29,f58])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ~m1_funct_2(k1_tarski(sK2),sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f27,f53])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f26,f48])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    v1_funct_1(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (26987)------------------------------
% 0.21/0.55  % (26987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26987)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (26987)Memory used [KB]: 6140
% 0.21/0.55  % (26987)Time elapsed: 0.117 s
% 0.21/0.55  % (26987)------------------------------
% 0.21/0.55  % (26987)------------------------------
% 0.21/0.55  % (26984)Success in time 0.185 s
%------------------------------------------------------------------------------
