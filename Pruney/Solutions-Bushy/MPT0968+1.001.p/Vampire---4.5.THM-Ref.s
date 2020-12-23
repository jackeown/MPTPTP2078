%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0968+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 146 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  356 ( 648 expanded)
%              Number of equality atoms :   94 ( 191 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (18805)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f227,f241,f245,f265])).

fof(f265,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f263,f76])).

fof(f76,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f263,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f256,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK5
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f256,plain,
    ( sP0(sK5,k1_xboole_0)
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f226,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK6
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f226,plain,
    ( sP0(sK5,sK6)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl10_4
  <=> sP0(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f245,plain,
    ( spl10_1
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f242,f224,f81])).

% (18804)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f242,plain,
    ( k1_xboole_0 = sK6
    | ~ spl10_4 ),
    inference(resolution,[],[f226,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f241,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f235,f131])).

fof(f131,plain,(
    r1_tarski(k2_relat_1(sK7),sK6) ),
    inference(resolution,[],[f128,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f128,plain,(
    m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK6)) ),
    inference(resolution,[],[f127,f44])).

fof(f44,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
    & ( k1_xboole_0 = sK5
      | k1_xboole_0 != sK6 )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f11,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(sK7,k1_funct_2(sK5,sK6))
      & ( k1_xboole_0 = sK5
        | k1_xboole_0 != sK6 )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f235,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK6)
    | ~ spl10_3 ),
    inference(resolution,[],[f230,f111])).

fof(f111,plain,(
    ~ sP3(sK6,sK5,sK7) ),
    inference(resolution,[],[f110,f46])).

fof(f46,plain,(
    ~ r2_hidden(sK7,k1_funct_2(sK5,sK6)) ),
    inference(cnf_transformation,[],[f26])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X1,X0))
      | ~ sP3(X0,X1,X2) ) ),
    inference(resolution,[],[f62,f79])).

fof(f79,plain,(
    ! [X0,X1] : sP4(X0,X1,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP4(X0,X1,X2) )
      & ( sP4(X0,X1,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP4(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f23,f22])).

fof(f22,plain,(
    ! [X1,X0,X3] :
      ( sP3(X1,X0,X3)
    <=> ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X1)
          & k1_relat_1(X4) = X0
          & X3 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP3(X1,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ sP3(X1,X0,X4)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ( ~ sP3(X1,X0,sK8(X0,X1,X2))
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sP3(X1,X0,sK8(X0,X1,X2))
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X0,X4) )
            & ( sP3(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP3(X1,X0,X3)
            | ~ r2_hidden(X3,X2) )
          & ( sP3(X1,X0,X3)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP3(X1,X0,sK8(X0,X1,X2))
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sP3(X1,X0,sK8(X0,X1,X2))
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X0,X4) )
            & ( sP3(X1,X0,X4)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X0,X3)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X0,X3)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP3(X1,X0,X3) )
            & ( sP3(X1,X0,X3)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f230,plain,
    ( ! [X0] :
        ( sP3(X0,sK5,sK7)
        | ~ r1_tarski(k2_relat_1(sK7),X0) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f229,f91])).

fof(f91,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f49,f44])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f229,plain,
    ( ! [X0] :
        ( sP3(X0,sK5,sK7)
        | ~ r1_tarski(k2_relat_1(sK7),X0)
        | ~ v1_relat_1(sK7) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f228,f42])).

fof(f42,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f228,plain,
    ( ! [X0] :
        ( sP3(X0,sK5,sK7)
        | ~ r1_tarski(k2_relat_1(sK7),X0)
        | ~ v1_funct_1(sK7)
        | ~ v1_relat_1(sK7) )
    | ~ spl10_3 ),
    inference(superposition,[],[f78,f222])).

fof(f222,plain,
    ( sK5 = k1_relat_1(sK7)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl10_3
  <=> sK5 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f78,plain,(
    ! [X0,X3] :
      ( sP3(X0,k1_relat_1(X3),X3)
      | ~ r1_tarski(k2_relat_1(X3),X0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3] :
      ( sP3(X0,k1_relat_1(X3),X2)
      | ~ r1_tarski(k2_relat_1(X3),X0)
      | X2 != X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2)
      | ~ r1_tarski(k2_relat_1(X3),X0)
      | k1_relat_1(X3) != X1
      | X2 != X3
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ( r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X0)
          & k1_relat_1(sK9(X0,X1,X2)) = X1
          & sK9(X0,X1,X2) = X2
          & v1_funct_1(sK9(X0,X1,X2))
          & v1_relat_1(sK9(X0,X1,X2)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_tarski(k2_relat_1(X4),X0)
          & k1_relat_1(X4) = X1
          & X2 = X4
          & v1_funct_1(X4)
          & v1_relat_1(X4) )
     => ( r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X0)
        & k1_relat_1(sK9(X0,X1,X2)) = X1
        & sK9(X0,X1,X2) = X2
        & v1_funct_1(sK9(X0,X1,X2))
        & v1_relat_1(sK9(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_tarski(k2_relat_1(X3),X0)
            | k1_relat_1(X3) != X1
            | X2 != X3
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X0)
            & k1_relat_1(X4) = X1
            & X2 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X3] :
      ( ( sP3(X1,X0,X3)
        | ! [X4] :
            ( ~ r1_tarski(k2_relat_1(X4),X1)
            | k1_relat_1(X4) != X0
            | X3 != X4
            | ~ v1_funct_1(X4)
            | ~ v1_relat_1(X4) ) )
      & ( ? [X4] :
            ( r1_tarski(k2_relat_1(X4),X1)
            & k1_relat_1(X4) = X0
            & X3 = X4
            & v1_funct_1(X4)
            & v1_relat_1(X4) )
        | ~ sP3(X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f227,plain,
    ( spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f218,f224,f220])).

fof(f218,plain,
    ( sP0(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f217,f43])).

% (18783)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (18795)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f43,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f217,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | sP0(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(resolution,[],[f155,f44])).

fof(f155,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f153,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f17,f20,f19,f18])).

fof(f19,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f153,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f55,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f88,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f45,f85,f81])).

fof(f45,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
