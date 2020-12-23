%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 251 expanded)
%              Number of leaves         :   37 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  570 (1197 expanded)
%              Number of equality atoms :  109 ( 262 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f94,f98,f102,f106,f110,f114,f118,f145,f148,f159,f210,f224,f235,f248,f268,f270,f278,f286,f302,f323,f329])).

fof(f329,plain,
    ( ~ spl7_3
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f326,f208,f155,f108,f96])).

fof(f96,plain,
    ( spl7_3
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f108,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f155,plain,
    ( spl7_13
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f208,plain,
    ( spl7_22
  <=> ! [X1] : ~ r2_hidden(k4_tarski(sK2,X1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f326,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(resolution,[],[f209,f163])).

fof(f163,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK5(sK3,X0)),sK3)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( ! [X0] :
        ( sK0 != sK0
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(X0,sK5(sK3,X0)),sK3) )
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f161,f156])).

fof(f156,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK0 != k1_relset_1(sK0,sK1,sK3)
        | r2_hidden(k4_tarski(X0,sK5(sK3,X0)),sK3) )
    | ~ spl7_6 ),
    inference(resolution,[],[f74,f109])).

fof(f109,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
            & r2_hidden(sK6(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f39,f41,f40])).

fof(f40,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
        & r2_hidden(sK6(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f209,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(sK2,X1),sK3)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f323,plain,
    ( k1_xboole_0 != k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    | k1_xboole_0 != k1_funct_1(k5_relat_1(sK3,sK4),sK2)
    | k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f302,plain,
    ( ~ spl7_5
    | ~ spl7_4
    | spl7_37
    | spl7_32 ),
    inference(avatar_split_clause,[],[f293,f276,f300,f100,f104])).

fof(f104,plain,
    ( spl7_5
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f100,plain,
    ( spl7_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f300,plain,
    ( spl7_37
  <=> k1_xboole_0 = k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f276,plain,
    ( spl7_32
  <=> r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f293,plain,
    ( k1_xboole_0 = k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl7_32 ),
    inference(resolution,[],[f277,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

% (28611)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f277,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(sK4))
    | spl7_32 ),
    inference(avatar_component_clause,[],[f276])).

fof(f286,plain,
    ( ~ spl7_28
    | ~ spl7_29
    | spl7_34
    | spl7_27 ),
    inference(avatar_split_clause,[],[f273,f246,f284,f253,f250])).

fof(f250,plain,
    ( spl7_28
  <=> v1_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f253,plain,
    ( spl7_29
  <=> v1_funct_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f284,plain,
    ( spl7_34
  <=> k1_xboole_0 = k1_funct_1(k5_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f246,plain,
    ( spl7_27
  <=> r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f273,plain,
    ( k1_xboole_0 = k1_funct_1(k5_relat_1(sK3,sK4),sK2)
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | spl7_27 ),
    inference(resolution,[],[f247,f78])).

fof(f247,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,sK4)))
    | spl7_27 ),
    inference(avatar_component_clause,[],[f246])).

fof(f278,plain,
    ( ~ spl7_5
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_8
    | ~ spl7_18
    | ~ spl7_32
    | spl7_27 ),
    inference(avatar_split_clause,[],[f271,f246,f276,f189,f116,f132,f100,f104])).

fof(f132,plain,
    ( spl7_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f116,plain,
    ( spl7_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f189,plain,
    ( spl7_18
  <=> r2_hidden(sK2,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f271,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(sK4))
    | ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl7_27 ),
    inference(resolution,[],[f247,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f270,plain,
    ( ~ spl7_10
    | ~ spl7_8
    | ~ spl7_5
    | ~ spl7_4
    | spl7_29 ),
    inference(avatar_split_clause,[],[f269,f253,f100,f104,f116,f132])).

fof(f269,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl7_29 ),
    inference(resolution,[],[f254,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f254,plain,
    ( ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | spl7_29 ),
    inference(avatar_component_clause,[],[f253])).

fof(f268,plain,
    ( ~ spl7_10
    | ~ spl7_5
    | spl7_28 ),
    inference(avatar_split_clause,[],[f264,f250,f104,f132])).

fof(f264,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | spl7_28 ),
    inference(resolution,[],[f251,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f251,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | spl7_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f248,plain,
    ( ~ spl7_27
    | spl7_1
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f244,f233,f88,f246])).

fof(f88,plain,
    ( spl7_1
  <=> k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f233,plain,
    ( spl7_25
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,sK4)))
        | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f244,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,sK4)))
    | spl7_1
    | ~ spl7_25 ),
    inference(trivial_inequality_removal,[],[f240])).

fof(f240,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK2)) != k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    | ~ r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,sK4)))
    | spl7_1
    | ~ spl7_25 ),
    inference(superposition,[],[f89,f234])).

fof(f234,plain,
    ( ! [X0] :
        ( k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,sK4))) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f233])).

fof(f89,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f235,plain,
    ( spl7_25
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f229,f222,f100,f104,f233])).

fof(f222,plain,
    ( spl7_24
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(sK3,X3)))
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | k1_funct_1(k5_relat_1(sK3,X3),X2) = k1_funct_1(X3,k1_funct_1(sK3,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK4)
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,sK4)))
        | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(resolution,[],[f223,f101])).

fof(f101,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f223,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(sK3,X3)))
        | k1_funct_1(k5_relat_1(sK3,X3),X2) = k1_funct_1(X3,k1_funct_1(sK3,X2)) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f222])).

fof(f224,plain,
    ( ~ spl7_10
    | spl7_24
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f215,f116,f222,f132])).

fof(f215,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(sK3,X3)))
        | k1_funct_1(k5_relat_1(sK3,X3),X2) = k1_funct_1(X3,k1_funct_1(sK3,X2))
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3) )
    | ~ spl7_8 ),
    inference(resolution,[],[f61,f117])).

fof(f117,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(f210,plain,
    ( ~ spl7_10
    | ~ spl7_8
    | spl7_22
    | spl7_18 ),
    inference(avatar_split_clause,[],[f198,f189,f208,f116,f132])).

fof(f198,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(sK2,X1),sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | spl7_18 ),
    inference(resolution,[],[f190,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f190,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f159,plain,
    ( spl7_13
    | spl7_2
    | ~ spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f153,f108,f112,f92,f155])).

fof(f92,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f112,plain,
    ( spl7_7
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f153,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f66,f109])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f148,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl7_12 ),
    inference(resolution,[],[f144,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f144,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl7_12
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f145,plain,
    ( ~ spl7_12
    | ~ spl7_6
    | spl7_10 ),
    inference(avatar_split_clause,[],[f141,f132,f108,f143])).

fof(f141,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_6
    | spl7_10 ),
    inference(resolution,[],[f140,f109])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_10 ),
    inference(resolution,[],[f133,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f133,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f118,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f45,f116])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2))
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2))
            & k1_xboole_0 != X1
            & r2_hidden(X2,X0)
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k1_funct_1(k5_relat_1(sK3,X4),sK2) != k1_funct_1(X4,k1_funct_1(sK3,sK2))
          & k1_xboole_0 != sK1
          & r2_hidden(sK2,sK0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( k1_funct_1(k5_relat_1(sK3,X4),sK2) != k1_funct_1(X4,k1_funct_1(sK3,sK2))
        & k1_xboole_0 != sK1
        & r2_hidden(sK2,sK0)
        & v1_funct_1(X4)
        & v1_relat_1(X4) )
   => ( k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2))
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2))
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2))
          & k1_xboole_0 != X1
          & r2_hidden(X2,X0)
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_relat_1(X4) )
           => ( r2_hidden(X2,X0)
             => ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
                | k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2))
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

fof(f114,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f46,f112])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f110,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f47,f108])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f48,f104])).

fof(f48,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f49,f100])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f50,f96])).

fof(f50,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f51,f92])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f52,f88])).

fof(f52,plain,(
    k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:21:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (28612)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (28616)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (28612)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f331,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f90,f94,f98,f102,f106,f110,f114,f118,f145,f148,f159,f210,f224,f235,f248,f268,f270,f278,f286,f302,f323,f329])).
% 0.22/0.48  fof(f329,plain,(
% 0.22/0.48    ~spl7_3 | ~spl7_6 | ~spl7_13 | ~spl7_22),
% 0.22/0.48    inference(avatar_split_clause,[],[f326,f208,f155,f108,f96])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    spl7_3 <=> r2_hidden(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    spl7_13 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.48  fof(f208,plain,(
% 0.22/0.48    spl7_22 <=> ! [X1] : ~r2_hidden(k4_tarski(sK2,X1),sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.48  fof(f326,plain,(
% 0.22/0.48    ~r2_hidden(sK2,sK0) | (~spl7_6 | ~spl7_13 | ~spl7_22)),
% 0.22/0.48    inference(resolution,[],[f209,f163])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK5(sK3,X0)),sK3) | ~r2_hidden(X0,sK0)) ) | (~spl7_6 | ~spl7_13)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f162])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    ( ! [X0] : (sK0 != sK0 | ~r2_hidden(X0,sK0) | r2_hidden(k4_tarski(X0,sK5(sK3,X0)),sK3)) ) | (~spl7_6 | ~spl7_13)),
% 0.22/0.48    inference(forward_demodulation,[],[f161,f156])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f155])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | sK0 != k1_relset_1(sK0,sK1,sK3) | r2_hidden(k4_tarski(X0,sK5(sK3,X0)),sK3)) ) | ~spl7_6),
% 0.22/0.48    inference(resolution,[],[f74,f109])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f108])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) & r2_hidden(sK6(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f39,f41,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) & r2_hidden(sK6(X1,X2),X1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.48    inference(rectify,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.48    inference(nnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.22/0.48  fof(f209,plain,(
% 0.22/0.48    ( ! [X1] : (~r2_hidden(k4_tarski(sK2,X1),sK3)) ) | ~spl7_22),
% 0.22/0.48    inference(avatar_component_clause,[],[f208])).
% 0.22/0.48  fof(f323,plain,(
% 0.22/0.48    k1_xboole_0 != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) | k1_xboole_0 != k1_funct_1(k5_relat_1(sK3,sK4),sK2) | k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2))),
% 0.22/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.48  fof(f302,plain,(
% 0.22/0.48    ~spl7_5 | ~spl7_4 | spl7_37 | spl7_32),
% 0.22/0.48    inference(avatar_split_clause,[],[f293,f276,f300,f100,f104])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    spl7_5 <=> v1_relat_1(sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    spl7_4 <=> v1_funct_1(sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.48  fof(f300,plain,(
% 0.22/0.48    spl7_37 <=> k1_xboole_0 = k1_funct_1(sK4,k1_funct_1(sK3,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.22/0.48  fof(f276,plain,(
% 0.22/0.48    spl7_32 <=> r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(sK4))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.22/0.48  fof(f293,plain,(
% 0.22/0.48    k1_xboole_0 = k1_funct_1(sK4,k1_funct_1(sK3,sK2)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl7_32),
% 0.22/0.48    inference(resolution,[],[f277,f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(X0,X1) = k1_xboole_0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f57])).
% 0.22/0.48  % (28611)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.48  fof(f277,plain,(
% 0.22/0.48    ~r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(sK4)) | spl7_32),
% 0.22/0.48    inference(avatar_component_clause,[],[f276])).
% 0.22/0.48  fof(f286,plain,(
% 0.22/0.48    ~spl7_28 | ~spl7_29 | spl7_34 | spl7_27),
% 0.22/0.48    inference(avatar_split_clause,[],[f273,f246,f284,f253,f250])).
% 0.22/0.48  fof(f250,plain,(
% 0.22/0.48    spl7_28 <=> v1_relat_1(k5_relat_1(sK3,sK4))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.48  fof(f253,plain,(
% 0.22/0.48    spl7_29 <=> v1_funct_1(k5_relat_1(sK3,sK4))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.22/0.48  fof(f284,plain,(
% 0.22/0.48    spl7_34 <=> k1_xboole_0 = k1_funct_1(k5_relat_1(sK3,sK4),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.22/0.48  fof(f246,plain,(
% 0.22/0.48    spl7_27 <=> r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,sK4)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.48  fof(f273,plain,(
% 0.22/0.48    k1_xboole_0 = k1_funct_1(k5_relat_1(sK3,sK4),sK2) | ~v1_funct_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | spl7_27),
% 0.22/0.48    inference(resolution,[],[f247,f78])).
% 0.22/0.48  fof(f247,plain,(
% 0.22/0.48    ~r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,sK4))) | spl7_27),
% 0.22/0.48    inference(avatar_component_clause,[],[f246])).
% 0.22/0.48  fof(f278,plain,(
% 0.22/0.48    ~spl7_5 | ~spl7_4 | ~spl7_10 | ~spl7_8 | ~spl7_18 | ~spl7_32 | spl7_27),
% 0.22/0.48    inference(avatar_split_clause,[],[f271,f246,f276,f189,f116,f132,f100,f104])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    spl7_10 <=> v1_relat_1(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl7_8 <=> v1_funct_1(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.48  fof(f189,plain,(
% 0.22/0.48    spl7_18 <=> r2_hidden(sK2,k1_relat_1(sK3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.48  fof(f271,plain,(
% 0.22/0.48    ~r2_hidden(k1_funct_1(sK3,sK2),k1_relat_1(sK4)) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl7_27),
% 0.22/0.48    inference(resolution,[],[f247,f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.22/0.48  fof(f270,plain,(
% 0.22/0.48    ~spl7_10 | ~spl7_8 | ~spl7_5 | ~spl7_4 | spl7_29),
% 0.22/0.48    inference(avatar_split_clause,[],[f269,f253,f100,f104,f116,f132])).
% 0.22/0.48  fof(f269,plain,(
% 0.22/0.48    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl7_29),
% 0.22/0.48    inference(resolution,[],[f254,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.22/0.48  fof(f254,plain,(
% 0.22/0.48    ~v1_funct_1(k5_relat_1(sK3,sK4)) | spl7_29),
% 0.22/0.48    inference(avatar_component_clause,[],[f253])).
% 0.22/0.48  fof(f268,plain,(
% 0.22/0.48    ~spl7_10 | ~spl7_5 | spl7_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f264,f250,f104,f132])).
% 0.22/0.48  fof(f264,plain,(
% 0.22/0.48    ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | spl7_28),
% 0.22/0.48    inference(resolution,[],[f251,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.48  fof(f251,plain,(
% 0.22/0.48    ~v1_relat_1(k5_relat_1(sK3,sK4)) | spl7_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f250])).
% 0.22/0.48  fof(f248,plain,(
% 0.22/0.48    ~spl7_27 | spl7_1 | ~spl7_25),
% 0.22/0.48    inference(avatar_split_clause,[],[f244,f233,f88,f246])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    spl7_1 <=> k1_funct_1(k5_relat_1(sK3,sK4),sK2) = k1_funct_1(sK4,k1_funct_1(sK3,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.48  fof(f233,plain,(
% 0.22/0.48    spl7_25 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,sK4))) | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.48  fof(f244,plain,(
% 0.22/0.48    ~r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,sK4))) | (spl7_1 | ~spl7_25)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f240])).
% 0.22/0.48  fof(f240,plain,(
% 0.22/0.48    k1_funct_1(sK4,k1_funct_1(sK3,sK2)) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) | ~r2_hidden(sK2,k1_relat_1(k5_relat_1(sK3,sK4))) | (spl7_1 | ~spl7_25)),
% 0.22/0.48    inference(superposition,[],[f89,f234])).
% 0.22/0.48  fof(f234,plain,(
% 0.22/0.48    ( ! [X0] : (k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,sK4)))) ) | ~spl7_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f233])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) | spl7_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f88])).
% 0.22/0.48  fof(f235,plain,(
% 0.22/0.48    spl7_25 | ~spl7_5 | ~spl7_4 | ~spl7_24),
% 0.22/0.48    inference(avatar_split_clause,[],[f229,f222,f100,f104,f233])).
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    spl7_24 <=> ! [X3,X2] : (~r2_hidden(X2,k1_relat_1(k5_relat_1(sK3,X3))) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k1_funct_1(k5_relat_1(sK3,X3),X2) = k1_funct_1(X3,k1_funct_1(sK3,X2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.48  fof(f229,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(sK4) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK3,sK4))) | k1_funct_1(k5_relat_1(sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl7_4 | ~spl7_24)),
% 0.22/0.48    inference(resolution,[],[f223,f101])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    v1_funct_1(sK4) | ~spl7_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f100])).
% 0.22/0.48  fof(f223,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~v1_funct_1(X3) | ~v1_relat_1(X3) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(sK3,X3))) | k1_funct_1(k5_relat_1(sK3,X3),X2) = k1_funct_1(X3,k1_funct_1(sK3,X2))) ) | ~spl7_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f222])).
% 0.22/0.48  fof(f224,plain,(
% 0.22/0.48    ~spl7_10 | spl7_24 | ~spl7_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f215,f116,f222,f132])).
% 0.22/0.48  fof(f215,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(k5_relat_1(sK3,X3))) | k1_funct_1(k5_relat_1(sK3,X3),X2) = k1_funct_1(X3,k1_funct_1(sK3,X2)) | ~v1_relat_1(sK3) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) ) | ~spl7_8),
% 0.22/0.48    inference(resolution,[],[f61,f117])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    v1_funct_1(sK3) | ~spl7_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f116])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    ~spl7_10 | ~spl7_8 | spl7_22 | spl7_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f198,f189,f208,f116,f132])).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    ( ! [X1] : (~r2_hidden(k4_tarski(sK2,X1),sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | spl7_18),
% 0.22/0.48    inference(resolution,[],[f190,f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.48  fof(f190,plain,(
% 0.22/0.48    ~r2_hidden(sK2,k1_relat_1(sK3)) | spl7_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f189])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    spl7_13 | spl7_2 | ~spl7_7 | ~spl7_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f153,f108,f112,f92,f155])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    spl7_2 <=> k1_xboole_0 = sK1),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    spl7_7 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_6),
% 0.22/0.48    inference(resolution,[],[f66,f109])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(nnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(flattening,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    spl7_12),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    $false | spl7_12),
% 0.22/0.48    inference(resolution,[],[f144,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl7_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f143])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    spl7_12 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    ~spl7_12 | ~spl7_6 | spl7_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f141,f132,f108,f143])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl7_6 | spl7_10)),
% 0.22/0.48    inference(resolution,[],[f140,f109])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_10),
% 0.22/0.48    inference(resolution,[],[f133,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    ~v1_relat_1(sK3) | spl7_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f132])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    spl7_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f45,f116])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    v1_funct_1(sK3)),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    (k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v1_funct_1(sK4) & v1_relat_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f32,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (? [X4] : (k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2)) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v1_funct_1(X4) & v1_relat_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k1_funct_1(k5_relat_1(sK3,X4),sK2) != k1_funct_1(X4,k1_funct_1(sK3,sK2)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v1_funct_1(X4) & v1_relat_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ? [X4] : (k1_funct_1(k5_relat_1(sK3,X4),sK2) != k1_funct_1(X4,k1_funct_1(sK3,sK2)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v1_funct_1(X4) & v1_relat_1(X4)) => (k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (? [X4] : (k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2)) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v1_funct_1(X4) & v1_relat_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (? [X4] : (((k1_funct_1(k5_relat_1(X3,X4),X2) != k1_funct_1(X4,k1_funct_1(X3,X2)) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (v1_funct_1(X4) & v1_relat_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f11])).
% 0.22/0.49  fof(f11,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(k5_relat_1(X3,X4),X2) = k1_funct_1(X4,k1_funct_1(X3,X2)) | k1_xboole_0 = X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl7_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f46,f112])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl7_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f108])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    spl7_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f48,f104])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    v1_relat_1(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl7_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f49,f100])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    v1_funct_1(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f50,f96])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    r2_hidden(sK2,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ~spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f51,f92])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    k1_xboole_0 != sK1),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ~spl7_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f52,f88])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    k1_funct_1(k5_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,k1_funct_1(sK3,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (28612)------------------------------
% 0.22/0.49  % (28612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28612)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (28612)Memory used [KB]: 10874
% 0.22/0.49  % (28612)Time elapsed: 0.044 s
% 0.22/0.49  % (28612)------------------------------
% 0.22/0.49  % (28612)------------------------------
% 0.22/0.49  % (28605)Success in time 0.128 s
%------------------------------------------------------------------------------
