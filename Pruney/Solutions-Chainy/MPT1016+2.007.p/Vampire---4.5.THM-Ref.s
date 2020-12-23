%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 436 expanded)
%              Number of leaves         :   45 ( 180 expanded)
%              Depth                    :   13
%              Number of atoms          :  790 (2184 expanded)
%              Number of equality atoms :  142 ( 504 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f729,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f79,f84,f98,f117,f133,f141,f152,f176,f214,f227,f231,f246,f252,f258,f277,f323,f327,f341,f347,f372,f382,f418,f515,f527,f601,f641,f685,f719,f720,f728])).

fof(f728,plain,
    ( ~ spl7_1
    | spl7_3
    | ~ spl7_7
    | ~ spl7_71 ),
    inference(avatar_contradiction_clause,[],[f727])).

fof(f727,plain,
    ( $false
    | ~ spl7_1
    | spl7_3
    | ~ spl7_7
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f726,f97])).

fof(f97,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f726,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl7_1
    | spl7_3
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f725,f64])).

fof(f64,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f725,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_3
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f723,f74])).

fof(f74,plain,
    ( ~ v2_funct_1(sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f723,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_71 ),
    inference(trivial_inequality_removal,[],[f722])).

fof(f722,plain,
    ( sK4(sK1) != sK4(sK1)
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_71 ),
    inference(superposition,[],[f48,f718])).

fof(f718,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f716])).

fof(f716,plain,
    ( spl7_71
  <=> sK4(sK1) = sK5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f48,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f720,plain,
    ( spl7_62
    | ~ spl7_16
    | ~ spl7_21
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f697,f512,f211,f174,f564])).

fof(f564,plain,
    ( spl7_62
  <=> ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0)
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f174,plain,
    ( spl7_16
  <=> ! [X5,X4] :
        ( X4 = X5
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f211,plain,
    ( spl7_21
  <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f512,plain,
    ( spl7_56
  <=> r2_hidden(sK5(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f697,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0)
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_16
    | ~ spl7_21
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f693,f514])).

fof(f514,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f512])).

fof(f693,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0)
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK5(sK1),sK0) )
    | ~ spl7_16
    | ~ spl7_21 ),
    inference(superposition,[],[f175,f213])).

fof(f213,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f211])).

fof(f175,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | X4 = X5
        | ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f719,plain,
    ( spl7_71
    | ~ spl7_37
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f704,f564,f369,f716])).

fof(f369,plain,
    ( spl7_37
  <=> r2_hidden(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f704,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ spl7_37
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f703,f371])).

fof(f371,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f369])).

fof(f703,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ r2_hidden(sK4(sK1),sK0)
    | ~ spl7_62 ),
    inference(equality_resolution,[],[f565])).

fof(f565,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0)
        | sK5(sK1) = X0
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f564])).

fof(f685,plain,
    ( spl7_68
    | ~ spl7_1
    | ~ spl7_3
    | spl7_26
    | ~ spl7_27
    | ~ spl7_59
    | ~ spl7_67 ),
    inference(avatar_split_clause,[],[f678,f595,f525,f255,f249,f72,f62,f599])).

fof(f599,plain,
    ( spl7_68
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | k1_xboole_0 = X0
        | ~ v1_funct_2(sK1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f249,plain,
    ( spl7_26
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f255,plain,
    ( spl7_27
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f525,plain,
    ( spl7_59
  <=> ! [X1,X0] :
        ( sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3))
        | ~ v2_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(X0,sK0,X1)
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f595,plain,
    ( spl7_67
  <=> sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f678,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK1,sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_1
    | ~ spl7_3
    | spl7_26
    | ~ spl7_27
    | ~ spl7_59
    | ~ spl7_67 ),
    inference(subsumption_resolution,[],[f677,f251])).

fof(f251,plain,
    ( sK2 != sK3
    | spl7_26 ),
    inference(avatar_component_clause,[],[f249])).

fof(f677,plain,
    ( ! [X0] :
        ( sK2 = sK3
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK1,sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_59
    | ~ spl7_67 ),
    inference(forward_demodulation,[],[f676,f597])).

fof(f597,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f595])).

fof(f676,plain,
    ( ! [X0] :
        ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK1,sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_59 ),
    inference(forward_demodulation,[],[f675,f257])).

fof(f257,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f255])).

fof(f675,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK1,sK0,X0)
        | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
        | k1_xboole_0 = X0 )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_59 ),
    inference(subsumption_resolution,[],[f674,f73])).

fof(f73,plain,
    ( v2_funct_1(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f674,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK1,sK0,X0)
        | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
        | k1_xboole_0 = X0 )
    | ~ spl7_1
    | ~ spl7_59 ),
    inference(resolution,[],[f526,f64])).

fof(f526,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(X0,sK0,X1)
        | sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3))
        | k1_xboole_0 = X1 )
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f525])).

fof(f641,plain,
    ( ~ spl7_2
    | ~ spl7_5
    | spl7_25
    | ~ spl7_68 ),
    inference(avatar_contradiction_clause,[],[f640])).

fof(f640,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_5
    | spl7_25
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f619,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f619,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl7_2
    | ~ spl7_5
    | spl7_25
    | ~ spl7_68 ),
    inference(backward_demodulation,[],[f245,f609])).

fof(f609,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f608,f83])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f608,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_2
    | ~ spl7_68 ),
    inference(resolution,[],[f600,f69])).

fof(f69,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl7_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f600,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK1,sK0,X0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f599])).

fof(f245,plain,
    ( ~ r1_tarski(sK0,sK3)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl7_25
  <=> r1_tarski(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f601,plain,
    ( spl7_67
    | spl7_68
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f582,f416,f72,f62,f599,f595])).

fof(f416,plain,
    ( spl7_44
  <=> ! [X1,X0] :
        ( sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2))
        | ~ v2_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(X0,sK0,X1)
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f582,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK1,sK0,X0)
        | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
        | k1_xboole_0 = X0 )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f581,f73])).

fof(f581,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_2(sK1,sK0,X0)
        | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
        | k1_xboole_0 = X0 )
    | ~ spl7_1
    | ~ spl7_44 ),
    inference(resolution,[],[f417,f64])).

fof(f417,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(X0,sK0,X1)
        | sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2))
        | k1_xboole_0 = X1 )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f416])).

fof(f527,plain,
    ( spl7_59
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f376,f345,f525])).

fof(f345,plain,
    ( spl7_35
  <=> ! [X0] :
        ( sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3))
        | sP6(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f376,plain,
    ( ! [X0,X1] :
        ( sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3))
        | ~ v2_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(X0,sK0,X1)
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X1 )
    | ~ spl7_35 ),
    inference(resolution,[],[f346,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X1 ) ),
    inference(general_splitting,[],[f58,f59_D])).

fof(f59,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | sP6(X3,X0) ) ),
    inference(cnf_transformation,[],[f59_D])).

fof(f59_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X0)
          | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 )
    <=> ~ sP6(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f346,plain,
    ( ! [X0] :
        ( sP6(X0,sK0)
        | sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3)) )
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f345])).

fof(f515,plain,
    ( spl7_56
    | ~ spl7_9
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f509,f380,f114,f512])).

fof(f114,plain,
    ( spl7_9
  <=> v4_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f380,plain,
    ( spl7_38
  <=> ! [X0] :
        ( r2_hidden(sK5(sK1),X0)
        | ~ v4_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f509,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ spl7_9
    | ~ spl7_38 ),
    inference(resolution,[],[f381,f116])).

fof(f116,plain,
    ( v4_relat_1(sK1,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f381,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK1,X0)
        | r2_hidden(sK5(sK1),X0) )
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f380])).

fof(f418,plain,
    ( spl7_44
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f335,f321,f416])).

fof(f321,plain,
    ( spl7_32
  <=> ! [X0] :
        ( sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2))
        | sP6(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f335,plain,
    ( ! [X0,X1] :
        ( sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2))
        | ~ v2_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(X0,sK0,X1)
        | ~ v1_funct_1(X0)
        | k1_xboole_0 = X1 )
    | ~ spl7_32 ),
    inference(resolution,[],[f322,f60])).

fof(f322,plain,
    ( ! [X0] :
        ( sP6(X0,sK0)
        | sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2)) )
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f321])).

fof(f382,plain,
    ( spl7_38
    | ~ spl7_7
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f378,f325,f95,f380])).

fof(f325,plain,
    ( spl7_33
  <=> ! [X0] :
        ( r2_hidden(sK5(sK1),X0)
        | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f378,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1),X0)
        | ~ v4_relat_1(sK1,X0) )
    | ~ spl7_7
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f377,f97])).

fof(f377,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1),X0)
        | ~ v4_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_33 ),
    inference(resolution,[],[f326,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f326,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK1),X0)
        | r2_hidden(sK5(sK1),X0) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f325])).

fof(f372,plain,
    ( spl7_37
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f367,f339,f114,f369])).

fof(f339,plain,
    ( spl7_34
  <=> ! [X0] :
        ( r2_hidden(sK4(sK1),X0)
        | ~ v4_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f367,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(resolution,[],[f340,f116])).

fof(f340,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK1,X0)
        | r2_hidden(sK4(sK1),X0) )
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f339])).

fof(f347,plain,
    ( spl7_35
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f331,f149,f345])).

fof(f149,plain,
    ( spl7_13
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f331,plain,
    ( ! [X0] :
        ( sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3))
        | sP6(X0,sK0) )
    | ~ spl7_13 ),
    inference(resolution,[],[f151,f59])).

fof(f151,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f341,plain,
    ( spl7_34
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f337,f275,f95,f339])).

fof(f275,plain,
    ( spl7_30
  <=> ! [X0] :
        ( r2_hidden(sK4(sK1),X0)
        | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f337,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1),X0)
        | ~ v4_relat_1(sK1,X0) )
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f336,f97])).

fof(f336,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1),X0)
        | ~ v4_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_30 ),
    inference(resolution,[],[f276,f49])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK1),X0)
        | r2_hidden(sK4(sK1),X0) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f275])).

fof(f327,plain,
    ( spl7_33
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f273,f229,f325])).

fof(f229,plain,
    ( spl7_24
  <=> ! [X1] :
        ( r2_hidden(sK5(sK1),X1)
        | ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f273,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK1),X0)
        | ~ r1_tarski(k1_relat_1(sK1),X0) )
    | ~ spl7_24 ),
    inference(resolution,[],[f230,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f230,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))
        | r2_hidden(sK5(sK1),X1) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f229])).

fof(f323,plain,
    ( spl7_32
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f278,f76,f321])).

fof(f76,plain,
    ( spl7_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f278,plain,
    ( ! [X0] :
        ( sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2))
        | sP6(X0,sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f78,f59])).

fof(f78,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f277,plain,
    ( spl7_30
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f272,f225,f275])).

fof(f225,plain,
    ( spl7_23
  <=> ! [X1] :
        ( r2_hidden(sK4(sK1),X1)
        | ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f272,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1),X0)
        | ~ r1_tarski(k1_relat_1(sK1),X0) )
    | ~ spl7_23 ),
    inference(resolution,[],[f226,f53])).

fof(f226,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))
        | r2_hidden(sK4(sK1),X1) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f225])).

fof(f258,plain,
    ( spl7_27
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f253,f72,f255])).

fof(f253,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f41,f73])).

fof(f41,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(f252,plain,
    ( ~ spl7_26
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f247,f72,f249])).

fof(f247,plain,
    ( sK2 != sK3
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f42,f73])).

fof(f42,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f246,plain,
    ( ~ spl7_25
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f241,f149,f243])).

fof(f241,plain,
    ( ~ r1_tarski(sK0,sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f151,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f231,plain,
    ( spl7_24
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f165,f138,f229])).

fof(f138,plain,
    ( spl7_12
  <=> r2_hidden(sK5(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f165,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK1),X1)
        | ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) )
    | ~ spl7_12 ),
    inference(resolution,[],[f140,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f140,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f227,plain,
    ( spl7_23
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f162,f130,f225])).

fof(f130,plain,
    ( spl7_11
  <=> r2_hidden(sK4(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f162,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK1),X1)
        | ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) )
    | ~ spl7_11 ),
    inference(resolution,[],[f132,f51])).

fof(f132,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f214,plain,
    ( spl7_21
    | ~ spl7_1
    | spl7_3
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f155,f95,f72,f62,f211])).

fof(f155,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl7_1
    | spl7_3
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f154,f97])).

fof(f154,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f153,f64])).

fof(f153,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl7_3 ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f176,plain,
    ( spl7_16
    | spl7_3 ),
    inference(avatar_split_clause,[],[f167,f72,f174])).

fof(f167,plain,
    ( ! [X4,X5] :
        ( X4 = X5
        | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X4,sK0) )
    | spl7_3 ),
    inference(subsumption_resolution,[],[f38,f74])).

fof(f38,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f152,plain,
    ( spl7_13
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f147,f72,f149])).

fof(f147,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f40,f73])).

fof(f40,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f141,plain,
    ( spl7_12
    | ~ spl7_1
    | spl7_3
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f128,f95,f72,f62,f138])).

fof(f128,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ spl7_1
    | spl7_3
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f127,f97])).

fof(f127,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f126,f74])).

fof(f126,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f46,f64])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f133,plain,
    ( spl7_11
    | ~ spl7_1
    | spl7_3
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f120,f95,f72,f62,f130])).

fof(f120,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ spl7_1
    | spl7_3
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f119,f97])).

fof(f119,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f118,f74])).

fof(f118,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f45,f64])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f117,plain,
    ( spl7_9
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f103,f81,f114])).

fof(f103,plain,
    ( v4_relat_1(sK1,sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f56,f83])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f98,plain,
    ( spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f92,f81,f95])).

fof(f92,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_5 ),
    inference(resolution,[],[f55,f83])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f84,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f39,f76,f72])).

fof(f39,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:29:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (19659)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.47  % (19668)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.47  % (19668)Refutation not found, incomplete strategy% (19668)------------------------------
% 0.22/0.47  % (19668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (19668)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (19668)Memory used [KB]: 10618
% 0.22/0.48  % (19668)Time elapsed: 0.055 s
% 0.22/0.48  % (19668)------------------------------
% 0.22/0.48  % (19668)------------------------------
% 0.22/0.49  % (19659)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f729,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f65,f70,f79,f84,f98,f117,f133,f141,f152,f176,f214,f227,f231,f246,f252,f258,f277,f323,f327,f341,f347,f372,f382,f418,f515,f527,f601,f641,f685,f719,f720,f728])).
% 0.22/0.49  fof(f728,plain,(
% 0.22/0.49    ~spl7_1 | spl7_3 | ~spl7_7 | ~spl7_71),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f727])).
% 0.22/0.49  fof(f727,plain,(
% 0.22/0.49    $false | (~spl7_1 | spl7_3 | ~spl7_7 | ~spl7_71)),
% 0.22/0.49    inference(subsumption_resolution,[],[f726,f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    v1_relat_1(sK1) | ~spl7_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f95])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl7_7 <=> v1_relat_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.49  fof(f726,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | (~spl7_1 | spl7_3 | ~spl7_71)),
% 0.22/0.49    inference(subsumption_resolution,[],[f725,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    v1_funct_1(sK1) | ~spl7_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl7_1 <=> v1_funct_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.49  fof(f725,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl7_3 | ~spl7_71)),
% 0.22/0.49    inference(subsumption_resolution,[],[f723,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ~v2_funct_1(sK1) | spl7_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl7_3 <=> v2_funct_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.49  fof(f723,plain,(
% 0.22/0.49    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_71),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f722])).
% 0.22/0.49  fof(f722,plain,(
% 0.22/0.49    sK4(sK1) != sK4(sK1) | v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_71),
% 0.22/0.49    inference(superposition,[],[f48,f718])).
% 0.22/0.49  fof(f718,plain,(
% 0.22/0.49    sK4(sK1) = sK5(sK1) | ~spl7_71),
% 0.22/0.49    inference(avatar_component_clause,[],[f716])).
% 0.22/0.49  fof(f716,plain,(
% 0.22/0.49    spl7_71 <=> sK4(sK1) = sK5(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0] : (sK4(X0) != sK5(X0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f30,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(rectify,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.22/0.49  fof(f720,plain,(
% 0.22/0.49    spl7_62 | ~spl7_16 | ~spl7_21 | ~spl7_56),
% 0.22/0.49    inference(avatar_split_clause,[],[f697,f512,f211,f174,f564])).
% 0.22/0.49  fof(f564,plain,(
% 0.22/0.49    spl7_62 <=> ! [X0] : (k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    spl7_16 <=> ! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    spl7_21 <=> k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.49  fof(f512,plain,(
% 0.22/0.49    spl7_56 <=> r2_hidden(sK5(sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 0.22/0.49  fof(f697,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0)) ) | (~spl7_16 | ~spl7_21 | ~spl7_56)),
% 0.22/0.49    inference(subsumption_resolution,[],[f693,f514])).
% 0.22/0.49  fof(f514,plain,(
% 0.22/0.49    r2_hidden(sK5(sK1),sK0) | ~spl7_56),
% 0.22/0.49    inference(avatar_component_clause,[],[f512])).
% 0.22/0.49  fof(f693,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0) | ~r2_hidden(sK5(sK1),sK0)) ) | (~spl7_16 | ~spl7_21)),
% 0.22/0.49    inference(superposition,[],[f175,f213])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~spl7_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f211])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    ( ! [X4,X5] : (k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | X4 = X5 | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) ) | ~spl7_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f174])).
% 0.22/0.49  fof(f719,plain,(
% 0.22/0.49    spl7_71 | ~spl7_37 | ~spl7_62),
% 0.22/0.49    inference(avatar_split_clause,[],[f704,f564,f369,f716])).
% 0.22/0.49  fof(f369,plain,(
% 0.22/0.49    spl7_37 <=> r2_hidden(sK4(sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.22/0.49  fof(f704,plain,(
% 0.22/0.49    sK4(sK1) = sK5(sK1) | (~spl7_37 | ~spl7_62)),
% 0.22/0.49    inference(subsumption_resolution,[],[f703,f371])).
% 0.22/0.49  fof(f371,plain,(
% 0.22/0.49    r2_hidden(sK4(sK1),sK0) | ~spl7_37),
% 0.22/0.49    inference(avatar_component_clause,[],[f369])).
% 0.22/0.49  fof(f703,plain,(
% 0.22/0.49    sK4(sK1) = sK5(sK1) | ~r2_hidden(sK4(sK1),sK0) | ~spl7_62),
% 0.22/0.49    inference(equality_resolution,[],[f565])).
% 0.22/0.49  fof(f565,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,X0) | sK5(sK1) = X0 | ~r2_hidden(X0,sK0)) ) | ~spl7_62),
% 0.22/0.49    inference(avatar_component_clause,[],[f564])).
% 0.22/0.49  fof(f685,plain,(
% 0.22/0.49    spl7_68 | ~spl7_1 | ~spl7_3 | spl7_26 | ~spl7_27 | ~spl7_59 | ~spl7_67),
% 0.22/0.49    inference(avatar_split_clause,[],[f678,f595,f525,f255,f249,f72,f62,f599])).
% 0.22/0.49  fof(f599,plain,(
% 0.22/0.49    spl7_68 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK1,sK0,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    spl7_26 <=> sK2 = sK3),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.49  fof(f255,plain,(
% 0.22/0.49    spl7_27 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.49  fof(f525,plain,(
% 0.22/0.49    spl7_59 <=> ! [X1,X0] : (sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3)) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_2(X0,sK0,X1) | ~v1_funct_1(X0) | k1_xboole_0 = X1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 0.22/0.49  fof(f595,plain,(
% 0.22/0.49    spl7_67 <=> sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).
% 0.22/0.49  fof(f678,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK1,sK0,X0) | k1_xboole_0 = X0) ) | (~spl7_1 | ~spl7_3 | spl7_26 | ~spl7_27 | ~spl7_59 | ~spl7_67)),
% 0.22/0.49    inference(subsumption_resolution,[],[f677,f251])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    sK2 != sK3 | spl7_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f249])).
% 0.22/0.49  fof(f677,plain,(
% 0.22/0.49    ( ! [X0] : (sK2 = sK3 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK1,sK0,X0) | k1_xboole_0 = X0) ) | (~spl7_1 | ~spl7_3 | ~spl7_27 | ~spl7_59 | ~spl7_67)),
% 0.22/0.49    inference(forward_demodulation,[],[f676,f597])).
% 0.22/0.49  fof(f597,plain,(
% 0.22/0.49    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl7_67),
% 0.22/0.49    inference(avatar_component_clause,[],[f595])).
% 0.22/0.49  fof(f676,plain,(
% 0.22/0.49    ( ! [X0] : (sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK1,sK0,X0) | k1_xboole_0 = X0) ) | (~spl7_1 | ~spl7_3 | ~spl7_27 | ~spl7_59)),
% 0.22/0.49    inference(forward_demodulation,[],[f675,f257])).
% 0.22/0.49  fof(f257,plain,(
% 0.22/0.49    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl7_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f255])).
% 0.22/0.49  fof(f675,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK1,sK0,X0) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = X0) ) | (~spl7_1 | ~spl7_3 | ~spl7_59)),
% 0.22/0.49    inference(subsumption_resolution,[],[f674,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    v2_funct_1(sK1) | ~spl7_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f674,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK1,sK0,X0) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = X0) ) | (~spl7_1 | ~spl7_59)),
% 0.22/0.49    inference(resolution,[],[f526,f64])).
% 0.22/0.49  fof(f526,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_2(X0,sK0,X1) | sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3)) | k1_xboole_0 = X1) ) | ~spl7_59),
% 0.22/0.49    inference(avatar_component_clause,[],[f525])).
% 0.22/0.49  fof(f641,plain,(
% 0.22/0.49    ~spl7_2 | ~spl7_5 | spl7_25 | ~spl7_68),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f640])).
% 0.22/0.49  fof(f640,plain,(
% 0.22/0.49    $false | (~spl7_2 | ~spl7_5 | spl7_25 | ~spl7_68)),
% 0.22/0.49    inference(subsumption_resolution,[],[f619,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f619,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,sK3) | (~spl7_2 | ~spl7_5 | spl7_25 | ~spl7_68)),
% 0.22/0.49    inference(backward_demodulation,[],[f245,f609])).
% 0.22/0.49  fof(f609,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | (~spl7_2 | ~spl7_5 | ~spl7_68)),
% 0.22/0.49    inference(subsumption_resolution,[],[f608,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl7_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.49  fof(f608,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl7_2 | ~spl7_68)),
% 0.22/0.49    inference(resolution,[],[f600,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    v1_funct_2(sK1,sK0,sK0) | ~spl7_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl7_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.49  fof(f600,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_2(sK1,sK0,X0) | k1_xboole_0 = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | ~spl7_68),
% 0.22/0.49    inference(avatar_component_clause,[],[f599])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    ~r1_tarski(sK0,sK3) | spl7_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f243])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    spl7_25 <=> r1_tarski(sK0,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.49  fof(f601,plain,(
% 0.22/0.49    spl7_67 | spl7_68 | ~spl7_1 | ~spl7_3 | ~spl7_44),
% 0.22/0.49    inference(avatar_split_clause,[],[f582,f416,f72,f62,f599,f595])).
% 0.22/0.49  fof(f416,plain,(
% 0.22/0.49    spl7_44 <=> ! [X1,X0] : (sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2)) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_2(X0,sK0,X1) | ~v1_funct_1(X0) | k1_xboole_0 = X1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.22/0.49  fof(f582,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK1,sK0,X0) | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = X0) ) | (~spl7_1 | ~spl7_3 | ~spl7_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f581,f73])).
% 0.22/0.49  fof(f581,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_2(sK1,sK0,X0) | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = X0) ) | (~spl7_1 | ~spl7_44)),
% 0.22/0.49    inference(resolution,[],[f417,f64])).
% 0.22/0.49  fof(f417,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_2(X0,sK0,X1) | sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2)) | k1_xboole_0 = X1) ) | ~spl7_44),
% 0.22/0.49    inference(avatar_component_clause,[],[f416])).
% 0.22/0.49  fof(f527,plain,(
% 0.22/0.49    spl7_59 | ~spl7_35),
% 0.22/0.49    inference(avatar_split_clause,[],[f376,f345,f525])).
% 0.22/0.49  fof(f345,plain,(
% 0.22/0.49    spl7_35 <=> ! [X0] : (sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3)) | sP6(X0,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.22/0.49  fof(f376,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3)) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_2(X0,sK0,X1) | ~v1_funct_1(X0) | k1_xboole_0 = X1) ) | ~spl7_35),
% 0.22/0.49    inference(resolution,[],[f346,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~sP6(X3,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | k1_xboole_0 = X1) )),
% 0.22/0.49    inference(general_splitting,[],[f58,f59_D])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | sP6(X3,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f59_D])).
% 0.22/0.49  fof(f59_D,plain,(
% 0.22/0.49    ( ! [X0,X3] : (( ! [X2] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) ) <=> ~sP6(X3,X0)) )),
% 0.22/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.22/0.49  fof(f346,plain,(
% 0.22/0.49    ( ! [X0] : (sP6(X0,sK0) | sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3))) ) | ~spl7_35),
% 0.22/0.49    inference(avatar_component_clause,[],[f345])).
% 0.22/0.49  fof(f515,plain,(
% 0.22/0.49    spl7_56 | ~spl7_9 | ~spl7_38),
% 0.22/0.49    inference(avatar_split_clause,[],[f509,f380,f114,f512])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl7_9 <=> v4_relat_1(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.49  fof(f380,plain,(
% 0.22/0.49    spl7_38 <=> ! [X0] : (r2_hidden(sK5(sK1),X0) | ~v4_relat_1(sK1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.22/0.49  fof(f509,plain,(
% 0.22/0.49    r2_hidden(sK5(sK1),sK0) | (~spl7_9 | ~spl7_38)),
% 0.22/0.49    inference(resolution,[],[f381,f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    v4_relat_1(sK1,sK0) | ~spl7_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f114])).
% 0.22/0.49  fof(f381,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_relat_1(sK1,X0) | r2_hidden(sK5(sK1),X0)) ) | ~spl7_38),
% 0.22/0.49    inference(avatar_component_clause,[],[f380])).
% 0.22/0.49  fof(f418,plain,(
% 0.22/0.49    spl7_44 | ~spl7_32),
% 0.22/0.49    inference(avatar_split_clause,[],[f335,f321,f416])).
% 0.22/0.49  fof(f321,plain,(
% 0.22/0.49    spl7_32 <=> ! [X0] : (sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2)) | sP6(X0,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.22/0.49  fof(f335,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2)) | ~v2_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_2(X0,sK0,X1) | ~v1_funct_1(X0) | k1_xboole_0 = X1) ) | ~spl7_32),
% 0.22/0.49    inference(resolution,[],[f322,f60])).
% 0.22/0.49  fof(f322,plain,(
% 0.22/0.49    ( ! [X0] : (sP6(X0,sK0) | sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2))) ) | ~spl7_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f321])).
% 0.22/0.49  fof(f382,plain,(
% 0.22/0.49    spl7_38 | ~spl7_7 | ~spl7_33),
% 0.22/0.49    inference(avatar_split_clause,[],[f378,f325,f95,f380])).
% 0.22/0.49  fof(f325,plain,(
% 0.22/0.49    spl7_33 <=> ! [X0] : (r2_hidden(sK5(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.22/0.49  fof(f378,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK5(sK1),X0) | ~v4_relat_1(sK1,X0)) ) | (~spl7_7 | ~spl7_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f377,f97])).
% 0.22/0.49  fof(f377,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK5(sK1),X0) | ~v4_relat_1(sK1,X0) | ~v1_relat_1(sK1)) ) | ~spl7_33),
% 0.22/0.49    inference(resolution,[],[f326,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.49  fof(f326,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | r2_hidden(sK5(sK1),X0)) ) | ~spl7_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f325])).
% 0.22/0.49  fof(f372,plain,(
% 0.22/0.49    spl7_37 | ~spl7_9 | ~spl7_34),
% 0.22/0.49    inference(avatar_split_clause,[],[f367,f339,f114,f369])).
% 0.22/0.49  fof(f339,plain,(
% 0.22/0.49    spl7_34 <=> ! [X0] : (r2_hidden(sK4(sK1),X0) | ~v4_relat_1(sK1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.22/0.49  fof(f367,plain,(
% 0.22/0.49    r2_hidden(sK4(sK1),sK0) | (~spl7_9 | ~spl7_34)),
% 0.22/0.49    inference(resolution,[],[f340,f116])).
% 0.22/0.49  fof(f340,plain,(
% 0.22/0.49    ( ! [X0] : (~v4_relat_1(sK1,X0) | r2_hidden(sK4(sK1),X0)) ) | ~spl7_34),
% 0.22/0.49    inference(avatar_component_clause,[],[f339])).
% 0.22/0.49  fof(f347,plain,(
% 0.22/0.49    spl7_35 | ~spl7_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f331,f149,f345])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    spl7_13 <=> r2_hidden(sK3,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.49  fof(f331,plain,(
% 0.22/0.49    ( ! [X0] : (sK3 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK3)) | sP6(X0,sK0)) ) | ~spl7_13),
% 0.22/0.49    inference(resolution,[],[f151,f59])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    r2_hidden(sK3,sK0) | ~spl7_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f149])).
% 0.22/0.49  fof(f341,plain,(
% 0.22/0.49    spl7_34 | ~spl7_7 | ~spl7_30),
% 0.22/0.49    inference(avatar_split_clause,[],[f337,f275,f95,f339])).
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    spl7_30 <=> ! [X0] : (r2_hidden(sK4(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.22/0.49  fof(f337,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK4(sK1),X0) | ~v4_relat_1(sK1,X0)) ) | (~spl7_7 | ~spl7_30)),
% 0.22/0.49    inference(subsumption_resolution,[],[f336,f97])).
% 0.22/0.49  fof(f336,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK4(sK1),X0) | ~v4_relat_1(sK1,X0) | ~v1_relat_1(sK1)) ) | ~spl7_30),
% 0.22/0.49    inference(resolution,[],[f276,f49])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | r2_hidden(sK4(sK1),X0)) ) | ~spl7_30),
% 0.22/0.49    inference(avatar_component_clause,[],[f275])).
% 0.22/0.49  fof(f327,plain,(
% 0.22/0.49    spl7_33 | ~spl7_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f273,f229,f325])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    spl7_24 <=> ! [X1] : (r2_hidden(sK5(sK1),X1) | ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK5(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X0)) ) | ~spl7_24),
% 0.22/0.49    inference(resolution,[],[f230,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) | r2_hidden(sK5(sK1),X1)) ) | ~spl7_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f229])).
% 0.22/0.49  fof(f323,plain,(
% 0.22/0.49    spl7_32 | ~spl7_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f278,f76,f321])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl7_4 <=> r2_hidden(sK2,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    ( ! [X0] : (sK2 = k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK2)) | sP6(X0,sK0)) ) | ~spl7_4),
% 0.22/0.49    inference(resolution,[],[f78,f59])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    r2_hidden(sK2,sK0) | ~spl7_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    spl7_30 | ~spl7_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f272,f225,f275])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    spl7_23 <=> ! [X1] : (r2_hidden(sK4(sK1),X1) | ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK4(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X0)) ) | ~spl7_23),
% 0.22/0.49    inference(resolution,[],[f226,f53])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) | r2_hidden(sK4(sK1),X1)) ) | ~spl7_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f225])).
% 0.22/0.49  fof(f258,plain,(
% 0.22/0.49    spl7_27 | ~spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f253,f72,f255])).
% 0.22/0.49  fof(f253,plain,(
% 0.22/0.49    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl7_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f41,f73])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ((sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) | ~v2_funct_1(sK1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f27,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) | ~v2_funct_1(sK1)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) | v2_funct_1(sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.49    inference(rectify,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    ~spl7_26 | ~spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f247,f72,f249])).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    sK2 != sK3 | ~spl7_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f42,f73])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f246,plain,(
% 0.22/0.49    ~spl7_25 | ~spl7_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f241,f149,f243])).
% 0.22/0.49  fof(f241,plain,(
% 0.22/0.49    ~r1_tarski(sK0,sK3) | ~spl7_13),
% 0.22/0.49    inference(resolution,[],[f151,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    spl7_24 | ~spl7_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f165,f138,f229])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl7_12 <=> r2_hidden(sK5(sK1),k1_relat_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    ( ! [X1] : (r2_hidden(sK5(sK1),X1) | ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))) ) | ~spl7_12),
% 0.22/0.49    inference(resolution,[],[f140,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | ~spl7_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    spl7_23 | ~spl7_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f162,f130,f225])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl7_11 <=> r2_hidden(sK4(sK1),k1_relat_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ( ! [X1] : (r2_hidden(sK4(sK1),X1) | ~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))) ) | ~spl7_11),
% 0.22/0.49    inference(resolution,[],[f132,f51])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | ~spl7_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f130])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    spl7_21 | ~spl7_1 | spl7_3 | ~spl7_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f155,f95,f72,f62,f211])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | (~spl7_1 | spl7_3 | ~spl7_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f154,f97])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | (~spl7_1 | spl7_3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f153,f64])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl7_3),
% 0.22/0.49    inference(resolution,[],[f74,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    spl7_16 | spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f167,f72,f174])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0)) ) | spl7_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f38,f74])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5) | ~r2_hidden(X5,sK0) | ~r2_hidden(X4,sK0) | v2_funct_1(sK1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    spl7_13 | ~spl7_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f147,f72,f149])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    r2_hidden(sK3,sK0) | ~spl7_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f40,f73])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    spl7_12 | ~spl7_1 | spl7_3 | ~spl7_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f128,f95,f72,f62,f138])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | (~spl7_1 | spl7_3 | ~spl7_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f127,f97])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl7_1 | spl7_3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f126,f74])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_1),
% 0.22/0.49    inference(resolution,[],[f46,f64])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl7_11 | ~spl7_1 | spl7_3 | ~spl7_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f120,f95,f72,f62,f130])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | (~spl7_1 | spl7_3 | ~spl7_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f119,f97])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl7_1 | spl7_3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f118,f74])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_1),
% 0.22/0.49    inference(resolution,[],[f45,f64])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    spl7_9 | ~spl7_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f103,f81,f114])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    v4_relat_1(sK1,sK0) | ~spl7_5),
% 0.22/0.49    inference(resolution,[],[f56,f83])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl7_7 | ~spl7_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f92,f81,f95])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    v1_relat_1(sK1) | ~spl7_5),
% 0.22/0.49    inference(resolution,[],[f55,f83])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl7_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f81])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ~spl7_3 | spl7_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f76,f72])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl7_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f67])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl7_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f62])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    v1_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (19659)------------------------------
% 0.22/0.49  % (19659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19659)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (19659)Memory used [KB]: 6524
% 0.22/0.49  % (19659)Time elapsed: 0.078 s
% 0.22/0.49  % (19659)------------------------------
% 0.22/0.49  % (19659)------------------------------
% 0.22/0.50  % (19656)Success in time 0.131 s
%------------------------------------------------------------------------------
