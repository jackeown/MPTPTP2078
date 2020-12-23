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
% DateTime   : Thu Dec  3 13:04:08 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 347 expanded)
%              Number of leaves         :   39 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  509 ( 893 expanded)
%              Number of equality atoms :  184 ( 380 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f951,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f197,f264,f364,f397,f398,f408,f430,f481,f544,f576,f578,f579,f688,f763,f904,f950])).

fof(f950,plain,(
    ~ spl4_49 ),
    inference(avatar_contradiction_clause,[],[f949])).

fof(f949,plain,
    ( $false
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f928,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f928,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ spl4_49 ),
    inference(resolution,[],[f903,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f903,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f901])).

fof(f901,plain,
    ( spl4_49
  <=> r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f904,plain,
    ( spl4_49
    | spl4_2
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_25
    | spl4_43 ),
    inference(avatar_split_clause,[],[f899,f760,f348,f334,f329,f114,f901])).

fof(f114,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f329,plain,
    ( spl4_22
  <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f334,plain,
    ( spl4_23
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f348,plain,
    ( spl4_25
  <=> k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f760,plain,
    ( spl4_43
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f899,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0)
    | spl4_2
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_25
    | spl4_43 ),
    inference(subsumption_resolution,[],[f891,f762])).

fof(f762,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl4_43 ),
    inference(avatar_component_clause,[],[f760])).

fof(f891,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl4_2
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(resolution,[],[f739,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

% (28568)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f739,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) )
    | spl4_2
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f738,f336])).

fof(f336,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f334])).

fof(f738,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ v1_funct_1(k1_xboole_0) )
    | spl4_2
    | ~ spl4_22
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f737,f331])).

fof(f331,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f329])).

fof(f737,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ v1_funct_1(k1_xboole_0) )
    | spl4_2
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f736,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f736,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
        | ~ v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ v1_funct_1(k1_xboole_0) )
    | spl4_2
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f734,f116])).

fof(f116,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f734,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
        | k1_xboole_0 = sK1
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
        | ~ v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl4_25 ),
    inference(superposition,[],[f75,f350])).

fof(f350,plain,
    ( k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f348])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f763,plain,
    ( ~ spl4_43
    | ~ spl4_7
    | ~ spl4_13
    | spl4_39 ),
    inference(avatar_split_clause,[],[f750,f573,f220,f140,f760])).

fof(f140,plain,
    ( spl4_7
  <=> ! [X3] :
        ( k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))
        | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f220,plain,
    ( spl4_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f573,plain,
    ( spl4_39
  <=> k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f750,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl4_7
    | ~ spl4_13
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f575,f345])).

fof(f345,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k2_enumset1(X3,X3,X3,X3)
        | k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3)) )
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f344,f55])).

fof(f55,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f344,plain,
    ( ! [X3] :
        ( k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3))
        | k1_xboole_0 != k2_enumset1(X3,X3,X3,X3) )
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f343,f222])).

fof(f222,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f220])).

fof(f343,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k2_enumset1(X3,X3,X3,X3)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) )
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f321,f54])).

fof(f54,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

% (28574)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f321,plain,
    ( ! [X3] :
        ( k1_relat_1(k1_xboole_0) != k2_enumset1(X3,X3,X3,X3)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) )
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f141,f222])).

% (28579)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f141,plain,
    ( ! [X3] :
        ( k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f575,plain,
    ( k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f573])).

fof(f688,plain,
    ( spl4_25
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f687,f220,f199,f348])).

fof(f199,plain,
    ( spl4_10
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f687,plain,
    ( k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f675,f55])).

fof(f675,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f201,f222])).

fof(f201,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f199])).

fof(f579,plain,
    ( spl4_22
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f318,f220,f124,f329])).

fof(f124,plain,
    ( spl4_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f318,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f126,f222])).

fof(f126,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f578,plain,
    ( spl4_23
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f319,f220,f129,f334])).

fof(f129,plain,
    ( spl4_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f319,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f131,f222])).

fof(f131,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f576,plain,
    ( ~ spl4_39
    | ~ spl4_13
    | spl4_16 ),
    inference(avatar_split_clause,[],[f361,f261,f220,f573])).

fof(f261,plain,
    ( spl4_16
  <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f361,plain,
    ( k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))
    | ~ spl4_13
    | spl4_16 ),
    inference(forward_demodulation,[],[f327,f55])).

fof(f327,plain,
    ( k2_relat_1(k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))
    | ~ spl4_13
    | spl4_16 ),
    inference(backward_demodulation,[],[f263,f222])).

fof(f263,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f261])).

fof(f544,plain,
    ( spl4_12
    | spl4_18
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f536,f247,f285,f216])).

fof(f216,plain,
    ( spl4_12
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f285,plain,
    ( spl4_18
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f247,plain,
    ( spl4_15
  <=> r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f536,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(duplicate_literal_removal,[],[f526])).

fof(f526,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(resolution,[],[f249,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f76,f70,f85,f85,f85,f86,f86,f86,f70])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f85])).

% (28567)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f249,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f247])).

fof(f481,plain,
    ( ~ spl4_18
    | ~ spl4_7
    | spl4_16 ),
    inference(avatar_split_clause,[],[f472,f261,f140,f285])).

% (28567)Refutation not found, incomplete strategy% (28567)------------------------------
% (28567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28567)Termination reason: Refutation not found, incomplete strategy

% (28567)Memory used [KB]: 10618
% (28567)Time elapsed: 0.147 s
% (28567)------------------------------
% (28567)------------------------------
fof(f472,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2)
    | ~ spl4_7
    | spl4_16 ),
    inference(unit_resulting_resolution,[],[f263,f141])).

fof(f430,plain,
    ( spl4_15
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f421,f204,f136,f247])).

fof(f136,plain,
    ( spl4_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f204,plain,
    ( spl4_11
  <=> v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f421,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f137,f206,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f206,plain,
    ( v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f204])).

fof(f137,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f408,plain,
    ( ~ spl4_12
    | ~ spl4_6
    | spl4_13 ),
    inference(avatar_split_clause,[],[f399,f220,f136,f216])).

fof(f399,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl4_6
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f137,f221,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f221,plain,
    ( k1_xboole_0 != sK2
    | spl4_13 ),
    inference(avatar_component_clause,[],[f220])).

fof(f398,plain,
    ( spl4_10
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f385,f119,f199])).

fof(f119,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f385,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f121,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f121,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f397,plain,
    ( spl4_11
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f384,f119,f204])).

fof(f384,plain,
    ( v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f121,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f364,plain,
    ( ~ spl4_6
    | spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f363,f129,f140,f136])).

fof(f363,plain,
    ( ! [X3] :
        ( k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))
        | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f131,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f68,f86,f86])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f264,plain,
    ( ~ spl4_16
    | spl4_1
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f251,f199,f109,f261])).

fof(f109,plain,
    ( spl4_1
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f251,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | spl4_1
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f111,f201])).

fof(f111,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f197,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f177,f119,f136])).

fof(f177,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f121,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f132,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f48,f129])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f127,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f89,f124])).

fof(f89,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f49,f86])).

fof(f49,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f122,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f88,f119])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f50,f86])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f51,f114])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f112,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f87,f109])).

fof(f87,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f52,f86,f86])).

fof(f52,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:56:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (28554)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (28575)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (28551)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (28572)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (28560)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (28563)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (28554)Refutation not found, incomplete strategy% (28554)------------------------------
% 0.21/0.56  % (28554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28572)Refutation not found, incomplete strategy% (28572)------------------------------
% 0.21/0.56  % (28572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28554)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28554)Memory used [KB]: 6268
% 0.21/0.56  % (28554)Time elapsed: 0.123 s
% 0.21/0.56  % (28554)------------------------------
% 0.21/0.56  % (28554)------------------------------
% 0.21/0.56  % (28572)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28572)Memory used [KB]: 10746
% 0.21/0.56  % (28572)Time elapsed: 0.133 s
% 0.21/0.56  % (28572)------------------------------
% 0.21/0.56  % (28572)------------------------------
% 0.21/0.57  % (28560)Refutation not found, incomplete strategy% (28560)------------------------------
% 0.21/0.57  % (28560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (28560)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (28560)Memory used [KB]: 10618
% 0.21/0.57  % (28560)Time elapsed: 0.142 s
% 0.21/0.57  % (28560)------------------------------
% 0.21/0.57  % (28560)------------------------------
% 0.21/0.57  % (28555)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (28550)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.58  % (28552)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.73/0.59  % (28564)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.73/0.59  % (28556)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.73/0.59  % (28561)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.73/0.59  % (28559)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.73/0.59  % (28555)Refutation not found, incomplete strategy% (28555)------------------------------
% 1.73/0.59  % (28555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (28555)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.59  
% 1.73/0.59  % (28555)Memory used [KB]: 6396
% 1.73/0.59  % (28555)Time elapsed: 0.165 s
% 1.73/0.59  % (28555)------------------------------
% 1.73/0.59  % (28555)------------------------------
% 1.73/0.59  % (28565)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.73/0.59  % (28553)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.73/0.60  % (28578)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.73/0.60  % (28570)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.73/0.60  % (28576)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.73/0.60  % (28573)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.73/0.60  % (28558)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.73/0.60  % (28566)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.90/0.60  % (28562)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.90/0.60  % (28575)Refutation found. Thanks to Tanya!
% 1.90/0.60  % SZS status Theorem for theBenchmark
% 1.90/0.60  % SZS output start Proof for theBenchmark
% 1.90/0.60  fof(f951,plain,(
% 1.90/0.60    $false),
% 1.90/0.60    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f197,f264,f364,f397,f398,f408,f430,f481,f544,f576,f578,f579,f688,f763,f904,f950])).
% 1.90/0.60  fof(f950,plain,(
% 1.90/0.60    ~spl4_49),
% 1.90/0.60    inference(avatar_contradiction_clause,[],[f949])).
% 1.90/0.60  fof(f949,plain,(
% 1.90/0.60    $false | ~spl4_49),
% 1.90/0.60    inference(subsumption_resolution,[],[f928,f56])).
% 1.90/0.60  fof(f56,plain,(
% 1.90/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f2])).
% 1.90/0.60  fof(f2,axiom,(
% 1.90/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.90/0.60  fof(f928,plain,(
% 1.90/0.60    ~r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))) | ~spl4_49),
% 1.90/0.60    inference(resolution,[],[f903,f69])).
% 1.90/0.60  fof(f69,plain,(
% 1.90/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f32])).
% 1.90/0.60  fof(f32,plain,(
% 1.90/0.60    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.90/0.60    inference(ennf_transformation,[],[f14])).
% 1.90/0.60  fof(f14,axiom,(
% 1.90/0.60    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.90/0.60  fof(f903,plain,(
% 1.90/0.60    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0) | ~spl4_49),
% 1.90/0.60    inference(avatar_component_clause,[],[f901])).
% 1.90/0.60  fof(f901,plain,(
% 1.90/0.60    spl4_49 <=> r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.90/0.60  fof(f904,plain,(
% 1.90/0.60    spl4_49 | spl4_2 | ~spl4_22 | ~spl4_23 | ~spl4_25 | spl4_43),
% 1.90/0.60    inference(avatar_split_clause,[],[f899,f760,f348,f334,f329,f114,f901])).
% 1.90/0.60  fof(f114,plain,(
% 1.90/0.60    spl4_2 <=> k1_xboole_0 = sK1),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.90/0.60  fof(f329,plain,(
% 1.90/0.60    spl4_22 <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.90/0.60  fof(f334,plain,(
% 1.90/0.60    spl4_23 <=> v1_funct_1(k1_xboole_0)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.90/0.60  fof(f348,plain,(
% 1.90/0.60    spl4_25 <=> k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.90/0.60  fof(f760,plain,(
% 1.90/0.60    spl4_43 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.90/0.60  fof(f899,plain,(
% 1.90/0.60    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0) | (spl4_2 | ~spl4_22 | ~spl4_23 | ~spl4_25 | spl4_43)),
% 1.90/0.60    inference(subsumption_resolution,[],[f891,f762])).
% 1.90/0.60  fof(f762,plain,(
% 1.90/0.60    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | spl4_43),
% 1.90/0.60    inference(avatar_component_clause,[],[f760])).
% 1.90/0.60  fof(f891,plain,(
% 1.90/0.60    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (spl4_2 | ~spl4_22 | ~spl4_23 | ~spl4_25)),
% 1.90/0.60    inference(resolution,[],[f739,f62])).
% 1.90/0.60  fof(f62,plain,(
% 1.90/0.60    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.90/0.60    inference(cnf_transformation,[],[f44])).
% 1.90/0.60  fof(f44,plain,(
% 1.90/0.60    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 1.90/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f43])).
% 1.90/0.60  fof(f43,plain,(
% 1.90/0.60    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 1.90/0.60    introduced(choice_axiom,[])).
% 1.90/0.60  fof(f28,plain,(
% 1.90/0.60    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.90/0.60    inference(ennf_transformation,[],[f18])).
% 1.90/0.60  fof(f18,axiom,(
% 1.90/0.60    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.90/0.60  % (28568)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.90/0.60  fof(f739,plain,(
% 1.90/0.60    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)) ) | (spl4_2 | ~spl4_22 | ~spl4_23 | ~spl4_25)),
% 1.90/0.60    inference(subsumption_resolution,[],[f738,f336])).
% 1.90/0.60  fof(f336,plain,(
% 1.90/0.60    v1_funct_1(k1_xboole_0) | ~spl4_23),
% 1.90/0.60    inference(avatar_component_clause,[],[f334])).
% 1.90/0.60  fof(f738,plain,(
% 1.90/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_funct_1(k1_xboole_0)) ) | (spl4_2 | ~spl4_22 | ~spl4_25)),
% 1.90/0.60    inference(subsumption_resolution,[],[f737,f331])).
% 1.90/0.60  fof(f331,plain,(
% 1.90/0.60    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl4_22),
% 1.90/0.60    inference(avatar_component_clause,[],[f329])).
% 1.90/0.60  fof(f737,plain,(
% 1.90/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(k1_xboole_0)) ) | (spl4_2 | ~spl4_25)),
% 1.90/0.60    inference(subsumption_resolution,[],[f736,f57])).
% 1.90/0.60  fof(f57,plain,(
% 1.90/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f7])).
% 1.90/0.60  fof(f7,axiom,(
% 1.90/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.90/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.90/0.60  fof(f736,plain,(
% 1.90/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(k1_xboole_0)) ) | (spl4_2 | ~spl4_25)),
% 1.90/0.60    inference(subsumption_resolution,[],[f734,f116])).
% 1.90/0.60  fof(f116,plain,(
% 1.90/0.60    k1_xboole_0 != sK1 | spl4_2),
% 1.90/0.60    inference(avatar_component_clause,[],[f114])).
% 1.90/0.60  fof(f734,plain,(
% 1.90/0.60    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | k1_xboole_0 = sK1 | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(k1_xboole_0)) ) | ~spl4_25),
% 1.90/0.60    inference(superposition,[],[f75,f350])).
% 1.90/0.60  fof(f350,plain,(
% 1.90/0.60    k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | ~spl4_25),
% 1.90/0.60    inference(avatar_component_clause,[],[f348])).
% 1.90/0.61  fof(f75,plain,(
% 1.90/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.90/0.61    inference(cnf_transformation,[],[f39])).
% 1.90/0.61  fof(f39,plain,(
% 1.90/0.61    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.90/0.61    inference(flattening,[],[f38])).
% 1.90/0.61  fof(f38,plain,(
% 1.90/0.61    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.90/0.61    inference(ennf_transformation,[],[f19])).
% 1.90/0.61  fof(f19,axiom,(
% 1.90/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 1.90/0.61  fof(f763,plain,(
% 1.90/0.61    ~spl4_43 | ~spl4_7 | ~spl4_13 | spl4_39),
% 1.90/0.61    inference(avatar_split_clause,[],[f750,f573,f220,f140,f760])).
% 1.90/0.61  fof(f140,plain,(
% 1.90/0.61    spl4_7 <=> ! [X3] : (k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2))),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.90/0.61  fof(f220,plain,(
% 1.90/0.61    spl4_13 <=> k1_xboole_0 = sK2),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.90/0.61  fof(f573,plain,(
% 1.90/0.61    spl4_39 <=> k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.90/0.61  fof(f750,plain,(
% 1.90/0.61    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | (~spl4_7 | ~spl4_13 | spl4_39)),
% 1.90/0.61    inference(unit_resulting_resolution,[],[f575,f345])).
% 1.90/0.61  fof(f345,plain,(
% 1.90/0.61    ( ! [X3] : (k1_xboole_0 != k2_enumset1(X3,X3,X3,X3) | k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3))) ) | (~spl4_7 | ~spl4_13)),
% 1.90/0.61    inference(forward_demodulation,[],[f344,f55])).
% 1.90/0.61  fof(f55,plain,(
% 1.90/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.90/0.61    inference(cnf_transformation,[],[f10])).
% 1.90/0.61  fof(f10,axiom,(
% 1.90/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.90/0.61  fof(f344,plain,(
% 1.90/0.61    ( ! [X3] : (k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3)) | k1_xboole_0 != k2_enumset1(X3,X3,X3,X3)) ) | (~spl4_7 | ~spl4_13)),
% 1.90/0.61    inference(forward_demodulation,[],[f343,f222])).
% 1.90/0.61  fof(f222,plain,(
% 1.90/0.61    k1_xboole_0 = sK2 | ~spl4_13),
% 1.90/0.61    inference(avatar_component_clause,[],[f220])).
% 1.90/0.61  fof(f343,plain,(
% 1.90/0.61    ( ! [X3] : (k1_xboole_0 != k2_enumset1(X3,X3,X3,X3) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) ) | (~spl4_7 | ~spl4_13)),
% 1.90/0.61    inference(forward_demodulation,[],[f321,f54])).
% 1.90/0.61  fof(f54,plain,(
% 1.90/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.90/0.61    inference(cnf_transformation,[],[f10])).
% 1.90/0.61  % (28574)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.90/0.61  fof(f321,plain,(
% 1.90/0.61    ( ! [X3] : (k1_relat_1(k1_xboole_0) != k2_enumset1(X3,X3,X3,X3) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) ) | (~spl4_7 | ~spl4_13)),
% 1.90/0.61    inference(backward_demodulation,[],[f141,f222])).
% 1.90/0.61  % (28579)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.90/0.61  fof(f141,plain,(
% 1.90/0.61    ( ! [X3] : (k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) ) | ~spl4_7),
% 1.90/0.61    inference(avatar_component_clause,[],[f140])).
% 1.90/0.61  fof(f575,plain,(
% 1.90/0.61    k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) | spl4_39),
% 1.90/0.61    inference(avatar_component_clause,[],[f573])).
% 1.90/0.61  fof(f688,plain,(
% 1.90/0.61    spl4_25 | ~spl4_10 | ~spl4_13),
% 1.90/0.61    inference(avatar_split_clause,[],[f687,f220,f199,f348])).
% 1.90/0.61  fof(f199,plain,(
% 1.90/0.61    spl4_10 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.90/0.61  fof(f687,plain,(
% 1.90/0.61    k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | (~spl4_10 | ~spl4_13)),
% 1.90/0.61    inference(forward_demodulation,[],[f675,f55])).
% 1.90/0.61  fof(f675,plain,(
% 1.90/0.61    k2_relat_1(k1_xboole_0) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | (~spl4_10 | ~spl4_13)),
% 1.90/0.61    inference(backward_demodulation,[],[f201,f222])).
% 1.90/0.61  fof(f201,plain,(
% 1.90/0.61    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) | ~spl4_10),
% 1.90/0.61    inference(avatar_component_clause,[],[f199])).
% 1.90/0.61  fof(f579,plain,(
% 1.90/0.61    spl4_22 | ~spl4_4 | ~spl4_13),
% 1.90/0.61    inference(avatar_split_clause,[],[f318,f220,f124,f329])).
% 1.90/0.61  fof(f124,plain,(
% 1.90/0.61    spl4_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.90/0.61  fof(f318,plain,(
% 1.90/0.61    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl4_4 | ~spl4_13)),
% 1.90/0.61    inference(backward_demodulation,[],[f126,f222])).
% 1.90/0.61  fof(f126,plain,(
% 1.90/0.61    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl4_4),
% 1.90/0.61    inference(avatar_component_clause,[],[f124])).
% 1.90/0.61  fof(f578,plain,(
% 1.90/0.61    spl4_23 | ~spl4_5 | ~spl4_13),
% 1.90/0.61    inference(avatar_split_clause,[],[f319,f220,f129,f334])).
% 1.90/0.61  fof(f129,plain,(
% 1.90/0.61    spl4_5 <=> v1_funct_1(sK2)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.90/0.61  fof(f319,plain,(
% 1.90/0.61    v1_funct_1(k1_xboole_0) | (~spl4_5 | ~spl4_13)),
% 1.90/0.61    inference(backward_demodulation,[],[f131,f222])).
% 1.90/0.61  fof(f131,plain,(
% 1.90/0.61    v1_funct_1(sK2) | ~spl4_5),
% 1.90/0.61    inference(avatar_component_clause,[],[f129])).
% 1.90/0.61  fof(f576,plain,(
% 1.90/0.61    ~spl4_39 | ~spl4_13 | spl4_16),
% 1.90/0.61    inference(avatar_split_clause,[],[f361,f261,f220,f573])).
% 1.90/0.61  fof(f261,plain,(
% 1.90/0.61    spl4_16 <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.90/0.61  fof(f361,plain,(
% 1.90/0.61    k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) | (~spl4_13 | spl4_16)),
% 1.90/0.61    inference(forward_demodulation,[],[f327,f55])).
% 1.90/0.61  fof(f327,plain,(
% 1.90/0.61    k2_relat_1(k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) | (~spl4_13 | spl4_16)),
% 1.90/0.61    inference(backward_demodulation,[],[f263,f222])).
% 1.90/0.61  fof(f263,plain,(
% 1.90/0.61    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | spl4_16),
% 1.90/0.61    inference(avatar_component_clause,[],[f261])).
% 1.90/0.61  fof(f544,plain,(
% 1.90/0.61    spl4_12 | spl4_18 | ~spl4_15),
% 1.90/0.61    inference(avatar_split_clause,[],[f536,f247,f285,f216])).
% 1.90/0.61  fof(f216,plain,(
% 1.90/0.61    spl4_12 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.90/0.61  fof(f285,plain,(
% 1.90/0.61    spl4_18 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.90/0.61  fof(f247,plain,(
% 1.90/0.61    spl4_15 <=> r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.90/0.61  fof(f536,plain,(
% 1.90/0.61    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | ~spl4_15),
% 1.90/0.61    inference(duplicate_literal_removal,[],[f526])).
% 1.90/0.61  fof(f526,plain,(
% 1.90/0.61    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | ~spl4_15),
% 1.90/0.61    inference(resolution,[],[f249,f99])).
% 1.90/0.61  fof(f99,plain,(
% 1.90/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 1.90/0.61    inference(definition_unfolding,[],[f76,f70,f85,f85,f85,f86,f86,f86,f70])).
% 1.90/0.61  fof(f86,plain,(
% 1.90/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.90/0.61    inference(definition_unfolding,[],[f58,f85])).
% 1.90/0.61  % (28567)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.90/0.61  fof(f58,plain,(
% 1.90/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.90/0.61    inference(cnf_transformation,[],[f3])).
% 1.90/0.61  fof(f3,axiom,(
% 1.90/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.90/0.61  fof(f85,plain,(
% 1.90/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.90/0.61    inference(definition_unfolding,[],[f65,f70])).
% 1.90/0.61  fof(f65,plain,(
% 1.90/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.90/0.61    inference(cnf_transformation,[],[f4])).
% 1.90/0.61  fof(f4,axiom,(
% 1.90/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.90/0.61  fof(f70,plain,(
% 1.90/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.90/0.61    inference(cnf_transformation,[],[f5])).
% 1.90/0.61  fof(f5,axiom,(
% 1.90/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.90/0.61  fof(f76,plain,(
% 1.90/0.61    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.90/0.61    inference(cnf_transformation,[],[f47])).
% 1.90/0.61  fof(f47,plain,(
% 1.90/0.61    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.90/0.61    inference(flattening,[],[f46])).
% 1.90/0.61  fof(f46,plain,(
% 1.90/0.61    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.90/0.61    inference(nnf_transformation,[],[f40])).
% 1.90/0.61  fof(f40,plain,(
% 1.90/0.61    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.90/0.61    inference(ennf_transformation,[],[f6])).
% 1.90/0.61  fof(f6,axiom,(
% 1.90/0.61    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.90/0.61  fof(f249,plain,(
% 1.90/0.61    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_15),
% 1.90/0.61    inference(avatar_component_clause,[],[f247])).
% 1.90/0.61  fof(f481,plain,(
% 1.90/0.61    ~spl4_18 | ~spl4_7 | spl4_16),
% 1.90/0.61    inference(avatar_split_clause,[],[f472,f261,f140,f285])).
% 1.90/0.61  % (28567)Refutation not found, incomplete strategy% (28567)------------------------------
% 1.90/0.61  % (28567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (28567)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.61  
% 1.90/0.61  % (28567)Memory used [KB]: 10618
% 1.90/0.61  % (28567)Time elapsed: 0.147 s
% 1.90/0.61  % (28567)------------------------------
% 1.90/0.61  % (28567)------------------------------
% 1.90/0.61  fof(f472,plain,(
% 1.90/0.61    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2) | (~spl4_7 | spl4_16)),
% 1.90/0.61    inference(unit_resulting_resolution,[],[f263,f141])).
% 1.90/0.61  fof(f430,plain,(
% 1.90/0.61    spl4_15 | ~spl4_6 | ~spl4_11),
% 1.90/0.61    inference(avatar_split_clause,[],[f421,f204,f136,f247])).
% 1.90/0.61  fof(f136,plain,(
% 1.90/0.61    spl4_6 <=> v1_relat_1(sK2)),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.90/0.61  fof(f204,plain,(
% 1.90/0.61    spl4_11 <=> v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.90/0.61  fof(f421,plain,(
% 1.90/0.61    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl4_6 | ~spl4_11)),
% 1.90/0.61    inference(unit_resulting_resolution,[],[f137,f206,f66])).
% 1.90/0.61  fof(f66,plain,(
% 1.90/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.90/0.61    inference(cnf_transformation,[],[f45])).
% 1.90/0.61  fof(f45,plain,(
% 1.90/0.61    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.90/0.61    inference(nnf_transformation,[],[f29])).
% 1.90/0.61  fof(f29,plain,(
% 1.90/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.90/0.61    inference(ennf_transformation,[],[f9])).
% 1.90/0.61  fof(f9,axiom,(
% 1.90/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.90/0.61  fof(f206,plain,(
% 1.90/0.61    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_11),
% 1.90/0.61    inference(avatar_component_clause,[],[f204])).
% 1.90/0.61  fof(f137,plain,(
% 1.90/0.61    v1_relat_1(sK2) | ~spl4_6),
% 1.90/0.61    inference(avatar_component_clause,[],[f136])).
% 1.90/0.61  fof(f408,plain,(
% 1.90/0.61    ~spl4_12 | ~spl4_6 | spl4_13),
% 1.90/0.61    inference(avatar_split_clause,[],[f399,f220,f136,f216])).
% 1.90/0.61  fof(f399,plain,(
% 1.90/0.61    k1_xboole_0 != k1_relat_1(sK2) | (~spl4_6 | spl4_13)),
% 1.90/0.61    inference(unit_resulting_resolution,[],[f137,f221,f60])).
% 1.90/0.61  fof(f60,plain,(
% 1.90/0.61    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.90/0.61    inference(cnf_transformation,[],[f27])).
% 1.90/0.61  fof(f27,plain,(
% 1.90/0.61    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.90/0.61    inference(flattening,[],[f26])).
% 1.90/0.61  fof(f26,plain,(
% 1.90/0.61    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.90/0.61    inference(ennf_transformation,[],[f11])).
% 1.90/0.61  fof(f11,axiom,(
% 1.90/0.61    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.90/0.61  fof(f221,plain,(
% 1.90/0.61    k1_xboole_0 != sK2 | spl4_13),
% 1.90/0.61    inference(avatar_component_clause,[],[f220])).
% 1.90/0.61  fof(f398,plain,(
% 1.90/0.61    spl4_10 | ~spl4_3),
% 1.90/0.61    inference(avatar_split_clause,[],[f385,f119,f199])).
% 1.90/0.61  fof(f119,plain,(
% 1.90/0.61    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.90/0.61  fof(f385,plain,(
% 1.90/0.61    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) | ~spl4_3),
% 1.90/0.61    inference(resolution,[],[f121,f72])).
% 1.90/0.61  fof(f72,plain,(
% 1.90/0.61    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.61    inference(cnf_transformation,[],[f34])).
% 1.90/0.61  fof(f34,plain,(
% 1.90/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.61    inference(ennf_transformation,[],[f17])).
% 1.90/0.61  fof(f17,axiom,(
% 1.90/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.90/0.61  fof(f121,plain,(
% 1.90/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl4_3),
% 1.90/0.61    inference(avatar_component_clause,[],[f119])).
% 1.90/0.61  fof(f397,plain,(
% 1.90/0.61    spl4_11 | ~spl4_3),
% 1.90/0.61    inference(avatar_split_clause,[],[f384,f119,f204])).
% 1.90/0.61  fof(f384,plain,(
% 1.90/0.61    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_3),
% 1.90/0.61    inference(resolution,[],[f121,f73])).
% 1.90/0.61  fof(f73,plain,(
% 1.90/0.61    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.61    inference(cnf_transformation,[],[f35])).
% 1.90/0.61  fof(f35,plain,(
% 1.90/0.61    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.61    inference(ennf_transformation,[],[f22])).
% 1.90/0.61  fof(f22,plain,(
% 1.90/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.90/0.61    inference(pure_predicate_removal,[],[f16])).
% 1.90/0.61  fof(f16,axiom,(
% 1.90/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.90/0.61  fof(f364,plain,(
% 1.90/0.61    ~spl4_6 | spl4_7 | ~spl4_5),
% 1.90/0.61    inference(avatar_split_clause,[],[f363,f129,f140,f136])).
% 1.90/0.61  fof(f363,plain,(
% 1.90/0.61    ( ! [X3] : (k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_5),
% 1.90/0.61    inference(resolution,[],[f131,f90])).
% 1.90/0.61  fof(f90,plain,(
% 1.90/0.61    ( ! [X0,X1] : (k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.90/0.61    inference(definition_unfolding,[],[f68,f86,f86])).
% 1.90/0.61  fof(f68,plain,(
% 1.90/0.61    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.90/0.61    inference(cnf_transformation,[],[f31])).
% 1.90/0.61  fof(f31,plain,(
% 1.90/0.61    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.90/0.61    inference(flattening,[],[f30])).
% 1.90/0.61  fof(f30,plain,(
% 1.90/0.61    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.90/0.61    inference(ennf_transformation,[],[f13])).
% 1.90/0.61  fof(f13,axiom,(
% 1.90/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.90/0.61  fof(f264,plain,(
% 1.90/0.61    ~spl4_16 | spl4_1 | ~spl4_10),
% 1.90/0.61    inference(avatar_split_clause,[],[f251,f199,f109,f261])).
% 1.90/0.61  fof(f109,plain,(
% 1.90/0.61    spl4_1 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.90/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.90/0.61  fof(f251,plain,(
% 1.90/0.61    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | (spl4_1 | ~spl4_10)),
% 1.90/0.61    inference(backward_demodulation,[],[f111,f201])).
% 1.90/0.61  fof(f111,plain,(
% 1.90/0.61    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) | spl4_1),
% 1.90/0.61    inference(avatar_component_clause,[],[f109])).
% 1.90/0.61  fof(f197,plain,(
% 1.90/0.61    spl4_6 | ~spl4_3),
% 1.90/0.61    inference(avatar_split_clause,[],[f177,f119,f136])).
% 1.90/0.61  fof(f177,plain,(
% 1.90/0.61    v1_relat_1(sK2) | ~spl4_3),
% 1.90/0.61    inference(unit_resulting_resolution,[],[f121,f71])).
% 1.90/0.61  fof(f71,plain,(
% 1.90/0.61    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.61    inference(cnf_transformation,[],[f33])).
% 1.90/0.61  fof(f33,plain,(
% 1.90/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.61    inference(ennf_transformation,[],[f15])).
% 1.90/0.61  fof(f15,axiom,(
% 1.90/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.90/0.61  fof(f132,plain,(
% 1.90/0.61    spl4_5),
% 1.90/0.61    inference(avatar_split_clause,[],[f48,f129])).
% 1.90/0.61  fof(f48,plain,(
% 1.90/0.61    v1_funct_1(sK2)),
% 1.90/0.61    inference(cnf_transformation,[],[f42])).
% 1.90/0.61  fof(f42,plain,(
% 1.90/0.61    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.90/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f41])).
% 1.90/0.61  fof(f41,plain,(
% 1.90/0.61    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.90/0.61    introduced(choice_axiom,[])).
% 1.90/0.61  fof(f24,plain,(
% 1.90/0.61    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.90/0.61    inference(flattening,[],[f23])).
% 1.90/0.61  fof(f23,plain,(
% 1.90/0.61    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.90/0.61    inference(ennf_transformation,[],[f21])).
% 1.90/0.61  fof(f21,negated_conjecture,(
% 1.90/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.90/0.61    inference(negated_conjecture,[],[f20])).
% 1.90/0.61  fof(f20,conjecture,(
% 1.90/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.90/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.90/0.61  fof(f127,plain,(
% 1.90/0.61    spl4_4),
% 1.90/0.61    inference(avatar_split_clause,[],[f89,f124])).
% 1.90/0.61  fof(f89,plain,(
% 1.90/0.61    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.90/0.61    inference(definition_unfolding,[],[f49,f86])).
% 1.90/0.61  fof(f49,plain,(
% 1.90/0.61    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.90/0.61    inference(cnf_transformation,[],[f42])).
% 1.90/0.61  fof(f122,plain,(
% 1.90/0.61    spl4_3),
% 1.90/0.61    inference(avatar_split_clause,[],[f88,f119])).
% 1.90/0.61  fof(f88,plain,(
% 1.90/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.90/0.61    inference(definition_unfolding,[],[f50,f86])).
% 1.90/0.61  fof(f50,plain,(
% 1.90/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.90/0.61    inference(cnf_transformation,[],[f42])).
% 1.90/0.61  fof(f117,plain,(
% 1.90/0.61    ~spl4_2),
% 1.90/0.61    inference(avatar_split_clause,[],[f51,f114])).
% 1.90/0.61  fof(f51,plain,(
% 1.90/0.61    k1_xboole_0 != sK1),
% 1.90/0.61    inference(cnf_transformation,[],[f42])).
% 1.90/0.61  fof(f112,plain,(
% 1.90/0.61    ~spl4_1),
% 1.90/0.61    inference(avatar_split_clause,[],[f87,f109])).
% 1.90/0.61  fof(f87,plain,(
% 1.90/0.61    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.90/0.61    inference(definition_unfolding,[],[f52,f86,f86])).
% 1.90/0.61  fof(f52,plain,(
% 1.90/0.61    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.90/0.61    inference(cnf_transformation,[],[f42])).
% 1.90/0.61  % SZS output end Proof for theBenchmark
% 1.90/0.61  % (28575)------------------------------
% 1.90/0.61  % (28575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (28575)Termination reason: Refutation
% 1.90/0.61  
% 1.90/0.61  % (28575)Memory used [KB]: 6652
% 1.90/0.61  % (28575)Time elapsed: 0.175 s
% 1.90/0.61  % (28575)------------------------------
% 1.90/0.61  % (28575)------------------------------
% 1.90/0.61  % (28549)Success in time 0.244 s
%------------------------------------------------------------------------------
