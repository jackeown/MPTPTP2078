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
% DateTime   : Thu Dec  3 13:04:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 355 expanded)
%              Number of leaves         :   39 ( 149 expanded)
%              Depth                    :   12
%              Number of atoms          :  521 ( 919 expanded)
%              Number of equality atoms :  184 ( 382 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f685,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f111,f116,f121,f126,f136,f189,f200,f201,f215,f242,f256,f302,f323,f338,f343,f348,f362,f377,f561,f657,f684])).

fof(f684,plain,(
    ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f683])).

fof(f683,plain,
    ( $false
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f663,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f663,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ spl4_36 ),
    inference(resolution,[],[f656,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f656,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl4_36
  <=> r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f657,plain,
    ( spl4_36
    | spl4_2
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_26
    | spl4_32 ),
    inference(avatar_split_clause,[],[f652,f558,f359,f345,f340,f335,f108,f654])).

fof(f108,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f335,plain,
    ( spl4_22
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f340,plain,
    ( spl4_23
  <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f345,plain,
    ( spl4_24
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f359,plain,
    ( spl4_26
  <=> k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f558,plain,
    ( spl4_32
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f652,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0)
    | spl4_2
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_26
    | spl4_32 ),
    inference(subsumption_resolution,[],[f644,f560])).

fof(f560,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f558])).

fof(f644,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl4_2
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(resolution,[],[f523,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f523,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) )
    | spl4_2
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f522,f347])).

fof(f347,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f345])).

fof(f522,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ v1_funct_1(k1_xboole_0) )
    | spl4_2
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f521,f342])).

fof(f342,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f340])).

fof(f521,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ v1_funct_1(k1_xboole_0) )
    | spl4_2
    | ~ spl4_22
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f520,f337])).

fof(f337,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f335])).

fof(f520,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
        | ~ v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ v1_funct_1(k1_xboole_0) )
    | spl4_2
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f518,f110])).

fof(f110,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f518,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
        | k1_xboole_0 = sK1
        | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
        | ~ v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl4_26 ),
    inference(superposition,[],[f69,f361])).

fof(f361,plain,
    ( k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f359])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f561,plain,
    ( ~ spl4_32
    | ~ spl4_7
    | ~ spl4_13
    | spl4_28 ),
    inference(avatar_split_clause,[],[f548,f374,f212,f134,f558])).

fof(f134,plain,
    ( spl4_7
  <=> ! [X3] :
        ( k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))
        | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f212,plain,
    ( spl4_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f374,plain,
    ( spl4_28
  <=> k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f548,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl4_7
    | ~ spl4_13
    | spl4_28 ),
    inference(unit_resulting_resolution,[],[f376,f356])).

fof(f356,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k2_enumset1(X3,X3,X3,X3)
        | k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3)) )
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f355,f50])).

fof(f50,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f355,plain,
    ( ! [X3] :
        ( k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3))
        | k1_xboole_0 != k2_enumset1(X3,X3,X3,X3) )
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f354,f214])).

fof(f214,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f212])).

fof(f354,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k2_enumset1(X3,X3,X3,X3)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) )
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f328,f49])).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f328,plain,
    ( ! [X3] :
        ( k1_relat_1(k1_xboole_0) != k2_enumset1(X3,X3,X3,X3)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) )
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f135,f214])).

fof(f135,plain,
    ( ! [X3] :
        ( k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f376,plain,
    ( k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f374])).

fof(f377,plain,
    ( ~ spl4_28
    | ~ spl4_13
    | spl4_16 ),
    inference(avatar_split_clause,[],[f371,f253,f212,f374])).

fof(f253,plain,
    ( spl4_16
  <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f371,plain,
    ( k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))
    | ~ spl4_13
    | spl4_16 ),
    inference(forward_demodulation,[],[f333,f50])).

fof(f333,plain,
    ( k2_relat_1(k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))
    | ~ spl4_13
    | spl4_16 ),
    inference(backward_demodulation,[],[f255,f214])).

fof(f255,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f253])).

fof(f362,plain,
    ( spl4_26
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f357,f212,f191,f359])).

fof(f191,plain,
    ( spl4_10
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f357,plain,
    ( k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f329,f50])).

fof(f329,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f193,f214])).

fof(f193,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f348,plain,
    ( spl4_24
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f326,f212,f123,f345])).

fof(f123,plain,
    ( spl4_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f326,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f125,f214])).

fof(f125,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f343,plain,
    ( spl4_23
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f325,f212,f118,f340])).

fof(f118,plain,
    ( spl4_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f325,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f120,f214])).

fof(f120,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f338,plain,
    ( spl4_22
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f324,f212,f113,f335])).

fof(f113,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f324,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f115,f214])).

fof(f115,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f323,plain,
    ( spl4_12
    | spl4_18
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f315,f239,f277,f208])).

% (31819)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f208,plain,
    ( spl4_12
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f277,plain,
    ( spl4_18
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f239,plain,
    ( spl4_15
  <=> r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f315,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(duplicate_literal_removal,[],[f305])).

fof(f305,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(resolution,[],[f241,f93])).

fof(f93,plain,(
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
    inference(definition_unfolding,[],[f70,f65,f79,f79,f79,f80,f80,f80,f65])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f79])).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f65])).

% (31818)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f241,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f239])).

fof(f302,plain,
    ( ~ spl4_18
    | ~ spl4_7
    | spl4_16 ),
    inference(avatar_split_clause,[],[f293,f253,f134,f277])).

fof(f293,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2)
    | ~ spl4_7
    | spl4_16 ),
    inference(unit_resulting_resolution,[],[f255,f135])).

fof(f256,plain,
    ( ~ spl4_16
    | spl4_1
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f243,f191,f103,f253])).

fof(f103,plain,
    ( spl4_1
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f243,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | spl4_1
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f105,f193])).

fof(f105,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f242,plain,
    ( spl4_15
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f229,f196,f130,f239])).

fof(f130,plain,
    ( spl4_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f196,plain,
    ( spl4_11
  <=> v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f229,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f131,f198,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f198,plain,
    ( v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f196])).

fof(f131,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f215,plain,
    ( ~ spl4_12
    | spl4_13
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f205,f130,f212,f208])).

fof(f205,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f131,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f201,plain,
    ( spl4_10
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f169,f113,f191])).

fof(f169,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f115,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f200,plain,
    ( spl4_11
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f168,f113,f196])).

fof(f168,plain,
    ( v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f115,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f189,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f170,f113,f130])).

fof(f170,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f115,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f136,plain,
    ( ~ spl4_6
    | spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f128,f123,f134,f130])).

fof(f128,plain,
    ( ! [X3] :
        ( k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))
        | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f125,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f63,f80,f80])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

% (31800)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f126,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f43,f123])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

% (31813)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f37,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f36])).

fof(f36,plain,
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

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

% (31796)Refutation not found, incomplete strategy% (31796)------------------------------
% (31796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31796)Termination reason: Refutation not found, incomplete strategy

% (31796)Memory used [KB]: 6268
% (31796)Time elapsed: 0.128 s
% (31796)------------------------------
% (31796)------------------------------
fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f121,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f83,f118])).

fof(f83,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f44,f80])).

fof(f44,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f116,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f82,f113])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f45,f80])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f111,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f46,f108])).

fof(f46,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f106,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f81,f103])).

fof(f81,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f47,f80,f80])).

fof(f47,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:55:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (31809)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (31817)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (31801)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (31797)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (31809)Refutation not found, incomplete strategy% (31809)------------------------------
% 0.22/0.52  % (31809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31792)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (31809)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31809)Memory used [KB]: 10618
% 0.22/0.52  % (31809)Time elapsed: 0.109 s
% 0.22/0.52  % (31809)------------------------------
% 0.22/0.52  % (31809)------------------------------
% 0.22/0.53  % (31798)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (31816)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (31795)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (31794)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (31793)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (31821)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (31817)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (31814)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (31820)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (31796)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f685,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f106,f111,f116,f121,f126,f136,f189,f200,f201,f215,f242,f256,f302,f323,f338,f343,f348,f362,f377,f561,f657,f684])).
% 0.22/0.54  fof(f684,plain,(
% 0.22/0.54    ~spl4_36),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f683])).
% 0.22/0.54  fof(f683,plain,(
% 0.22/0.54    $false | ~spl4_36),
% 0.22/0.54    inference(subsumption_resolution,[],[f663,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f663,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0)))) | ~spl4_36),
% 0.22/0.54    inference(resolution,[],[f656,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.54  fof(f656,plain,(
% 0.22/0.54    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0) | ~spl4_36),
% 0.22/0.54    inference(avatar_component_clause,[],[f654])).
% 0.22/0.54  fof(f654,plain,(
% 0.22/0.54    spl4_36 <=> r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.54  fof(f657,plain,(
% 0.22/0.54    spl4_36 | spl4_2 | ~spl4_22 | ~spl4_23 | ~spl4_24 | ~spl4_26 | spl4_32),
% 0.22/0.54    inference(avatar_split_clause,[],[f652,f558,f359,f345,f340,f335,f108,f654])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    spl4_2 <=> k1_xboole_0 = sK1),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.54  fof(f335,plain,(
% 0.22/0.54    spl4_22 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.54  fof(f340,plain,(
% 0.22/0.54    spl4_23 <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.54  fof(f345,plain,(
% 0.22/0.54    spl4_24 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.54  fof(f359,plain,(
% 0.22/0.54    spl4_26 <=> k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.54  fof(f558,plain,(
% 0.22/0.54    spl4_32 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.54  fof(f652,plain,(
% 0.22/0.54    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0) | (spl4_2 | ~spl4_22 | ~spl4_23 | ~spl4_24 | ~spl4_26 | spl4_32)),
% 0.22/0.54    inference(subsumption_resolution,[],[f644,f560])).
% 0.22/0.54  fof(f560,plain,(
% 0.22/0.54    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | spl4_32),
% 0.22/0.54    inference(avatar_component_clause,[],[f558])).
% 0.22/0.54  fof(f644,plain,(
% 0.22/0.54    r2_hidden(k1_funct_1(k1_xboole_0,sK3(k2_enumset1(sK0,sK0,sK0,sK0))),k1_xboole_0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (spl4_2 | ~spl4_22 | ~spl4_23 | ~spl4_24 | ~spl4_26)),
% 0.22/0.54    inference(resolution,[],[f523,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.22/0.54  fof(f523,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)) ) | (spl4_2 | ~spl4_22 | ~spl4_23 | ~spl4_24 | ~spl4_26)),
% 0.22/0.54    inference(subsumption_resolution,[],[f522,f347])).
% 0.22/0.54  fof(f347,plain,(
% 0.22/0.54    v1_funct_1(k1_xboole_0) | ~spl4_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f345])).
% 0.22/0.54  fof(f522,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_funct_1(k1_xboole_0)) ) | (spl4_2 | ~spl4_22 | ~spl4_23 | ~spl4_26)),
% 0.22/0.54    inference(subsumption_resolution,[],[f521,f342])).
% 0.22/0.54  fof(f342,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl4_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f340])).
% 0.22/0.54  fof(f521,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(k1_xboole_0)) ) | (spl4_2 | ~spl4_22 | ~spl4_26)),
% 0.22/0.54    inference(subsumption_resolution,[],[f520,f337])).
% 0.22/0.54  fof(f337,plain,(
% 0.22/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl4_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f335])).
% 0.22/0.54  fof(f520,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(k1_xboole_0)) ) | (spl4_2 | ~spl4_26)),
% 0.22/0.54    inference(subsumption_resolution,[],[f518,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    k1_xboole_0 != sK1 | spl4_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f108])).
% 0.22/0.54  fof(f518,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | k1_xboole_0 = sK1 | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~v1_funct_1(k1_xboole_0)) ) | ~spl4_26),
% 0.22/0.54    inference(superposition,[],[f69,f361])).
% 0.22/0.54  fof(f361,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | ~spl4_26),
% 0.22/0.54    inference(avatar_component_clause,[],[f359])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.54    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 0.22/0.54  fof(f561,plain,(
% 0.22/0.54    ~spl4_32 | ~spl4_7 | ~spl4_13 | spl4_28),
% 0.22/0.54    inference(avatar_split_clause,[],[f548,f374,f212,f134,f558])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl4_7 <=> ! [X3] : (k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    spl4_13 <=> k1_xboole_0 = sK2),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.54  fof(f374,plain,(
% 0.22/0.54    spl4_28 <=> k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.54  fof(f548,plain,(
% 0.22/0.54    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | (~spl4_7 | ~spl4_13 | spl4_28)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f376,f356])).
% 0.22/0.54  fof(f356,plain,(
% 0.22/0.54    ( ! [X3] : (k1_xboole_0 != k2_enumset1(X3,X3,X3,X3) | k1_xboole_0 = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3))) ) | (~spl4_7 | ~spl4_13)),
% 0.22/0.54    inference(forward_demodulation,[],[f355,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.54  fof(f355,plain,(
% 0.22/0.54    ( ! [X3] : (k2_relat_1(k1_xboole_0) = k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3)) | k1_xboole_0 != k2_enumset1(X3,X3,X3,X3)) ) | (~spl4_7 | ~spl4_13)),
% 0.22/0.54    inference(forward_demodulation,[],[f354,f214])).
% 0.22/0.54  fof(f214,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | ~spl4_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f212])).
% 0.22/0.54  fof(f354,plain,(
% 0.22/0.54    ( ! [X3] : (k1_xboole_0 != k2_enumset1(X3,X3,X3,X3) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) ) | (~spl4_7 | ~spl4_13)),
% 0.22/0.54    inference(forward_demodulation,[],[f328,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f328,plain,(
% 0.22/0.54    ( ! [X3] : (k1_relat_1(k1_xboole_0) != k2_enumset1(X3,X3,X3,X3) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) ) | (~spl4_7 | ~spl4_13)),
% 0.22/0.54    inference(backward_demodulation,[],[f135,f214])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X3] : (k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3))) ) | ~spl4_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f134])).
% 0.22/0.54  fof(f376,plain,(
% 0.22/0.54    k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) | spl4_28),
% 0.22/0.54    inference(avatar_component_clause,[],[f374])).
% 0.22/0.54  fof(f377,plain,(
% 0.22/0.54    ~spl4_28 | ~spl4_13 | spl4_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f371,f253,f212,f374])).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    spl4_16 <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.54  fof(f371,plain,(
% 0.22/0.54    k1_xboole_0 != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) | (~spl4_13 | spl4_16)),
% 0.22/0.54    inference(forward_demodulation,[],[f333,f50])).
% 0.22/0.54  fof(f333,plain,(
% 0.22/0.54    k2_relat_1(k1_xboole_0) != k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) | (~spl4_13 | spl4_16)),
% 0.22/0.54    inference(backward_demodulation,[],[f255,f214])).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | spl4_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f253])).
% 0.22/0.54  fof(f362,plain,(
% 0.22/0.54    spl4_26 | ~spl4_10 | ~spl4_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f357,f212,f191,f359])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    spl4_10 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.54  fof(f357,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | (~spl4_10 | ~spl4_13)),
% 0.22/0.54    inference(forward_demodulation,[],[f329,f50])).
% 0.22/0.54  fof(f329,plain,(
% 0.22/0.54    k2_relat_1(k1_xboole_0) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | (~spl4_10 | ~spl4_13)),
% 0.22/0.54    inference(backward_demodulation,[],[f193,f214])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) | ~spl4_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f191])).
% 0.22/0.54  fof(f348,plain,(
% 0.22/0.54    spl4_24 | ~spl4_5 | ~spl4_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f326,f212,f123,f345])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    spl4_5 <=> v1_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.54  fof(f326,plain,(
% 0.22/0.54    v1_funct_1(k1_xboole_0) | (~spl4_5 | ~spl4_13)),
% 0.22/0.54    inference(backward_demodulation,[],[f125,f214])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    v1_funct_1(sK2) | ~spl4_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f123])).
% 0.22/0.54  fof(f343,plain,(
% 0.22/0.54    spl4_23 | ~spl4_4 | ~spl4_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f325,f212,f118,f340])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    spl4_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.54  fof(f325,plain,(
% 0.22/0.54    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl4_4 | ~spl4_13)),
% 0.22/0.54    inference(backward_demodulation,[],[f120,f214])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl4_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f118])).
% 0.22/0.54  fof(f338,plain,(
% 0.22/0.54    spl4_22 | ~spl4_3 | ~spl4_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f324,f212,f113,f335])).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.55  fof(f324,plain,(
% 0.22/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | (~spl4_3 | ~spl4_13)),
% 0.22/0.55    inference(backward_demodulation,[],[f115,f214])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl4_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f113])).
% 0.22/0.55  fof(f323,plain,(
% 0.22/0.55    spl4_12 | spl4_18 | ~spl4_15),
% 0.22/0.55    inference(avatar_split_clause,[],[f315,f239,f277,f208])).
% 0.22/0.55  % (31819)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    spl4_12 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.55  fof(f277,plain,(
% 0.22/0.55    spl4_18 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.55  fof(f239,plain,(
% 0.22/0.55    spl4_15 <=> r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.55  fof(f315,plain,(
% 0.22/0.55    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | ~spl4_15),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f305])).
% 0.22/0.55  fof(f305,plain,(
% 0.22/0.55    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | ~spl4_15),
% 0.22/0.55    inference(resolution,[],[f241,f93])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f70,f65,f79,f79,f79,f80,f80,f80,f65])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f52,f79])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f60,f65])).
% 0.22/0.55  % (31818)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 0.22/0.55    inference(flattening,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 0.22/0.55    inference(nnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 0.22/0.55  fof(f241,plain,(
% 0.22/0.55    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_15),
% 0.22/0.55    inference(avatar_component_clause,[],[f239])).
% 0.22/0.55  fof(f302,plain,(
% 0.22/0.55    ~spl4_18 | ~spl4_7 | spl4_16),
% 0.22/0.55    inference(avatar_split_clause,[],[f293,f253,f134,f277])).
% 0.22/0.55  fof(f293,plain,(
% 0.22/0.55    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK2) | (~spl4_7 | spl4_16)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f255,f135])).
% 0.22/0.55  fof(f256,plain,(
% 0.22/0.55    ~spl4_16 | spl4_1 | ~spl4_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f243,f191,f103,f253])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    spl4_1 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | (spl4_1 | ~spl4_10)),
% 0.22/0.55    inference(backward_demodulation,[],[f105,f193])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) | spl4_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f103])).
% 0.22/0.55  fof(f242,plain,(
% 0.22/0.55    spl4_15 | ~spl4_6 | ~spl4_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f229,f196,f130,f239])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    spl4_6 <=> v1_relat_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.55  fof(f196,plain,(
% 0.22/0.55    spl4_11 <=> v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.55  fof(f229,plain,(
% 0.22/0.55    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl4_6 | ~spl4_11)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f131,f198,f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f196])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    v1_relat_1(sK2) | ~spl4_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f130])).
% 0.22/0.55  fof(f215,plain,(
% 0.22/0.55    ~spl4_12 | spl4_13 | ~spl4_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f205,f130,f212,f208])).
% 0.22/0.55  fof(f205,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | k1_xboole_0 != k1_relat_1(sK2) | ~spl4_6),
% 0.22/0.55    inference(resolution,[],[f131,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.55  fof(f201,plain,(
% 0.22/0.55    spl4_10 | ~spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f169,f113,f191])).
% 0.22/0.55  fof(f169,plain,(
% 0.22/0.55    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) | ~spl4_3),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f115,f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    spl4_11 | ~spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f168,f113,f196])).
% 0.22/0.55  fof(f168,plain,(
% 0.22/0.55    v4_relat_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_3),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f115,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    spl4_6 | ~spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f170,f113,f130])).
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    v1_relat_1(sK2) | ~spl4_3),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f115,f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ~spl4_6 | spl4_7 | ~spl4_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f128,f123,f134,f130])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    ( ! [X3] : (k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3),k1_funct_1(sK2,X3)) | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_5),
% 0.22/0.55    inference(resolution,[],[f125,f84])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f63,f80,f80])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.55  % (31800)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    spl4_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f43,f123])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  % (31813)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f19])).
% 0.22/0.55  % (31796)Refutation not found, incomplete strategy% (31796)------------------------------
% 0.22/0.55  % (31796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31796)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31796)Memory used [KB]: 6268
% 0.22/0.55  % (31796)Time elapsed: 0.128 s
% 0.22/0.55  % (31796)------------------------------
% 0.22/0.55  % (31796)------------------------------
% 0.22/0.55  fof(f19,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.22/0.55    inference(negated_conjecture,[],[f18])).
% 0.22/0.55  fof(f18,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    spl4_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f83,f118])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.55    inference(definition_unfolding,[],[f44,f80])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    spl4_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f82,f113])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.22/0.55    inference(definition_unfolding,[],[f45,f80])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    ~spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f46,f108])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    k1_xboole_0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ~spl4_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f81,f103])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 0.22/0.55    inference(definition_unfolding,[],[f47,f80,f80])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (31817)------------------------------
% 0.22/0.55  % (31817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31817)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (31817)Memory used [KB]: 6652
% 0.22/0.55  % (31817)Time elapsed: 0.127 s
% 0.22/0.55  % (31817)------------------------------
% 0.22/0.55  % (31817)------------------------------
% 0.22/0.55  % (31811)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (31810)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (31806)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (31791)Success in time 0.185 s
%------------------------------------------------------------------------------
