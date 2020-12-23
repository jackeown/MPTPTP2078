%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t34_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:22 EDT 2019

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 413 expanded)
%              Number of leaves         :   39 ( 175 expanded)
%              Depth                    :   14
%              Number of atoms          :  737 (1871 expanded)
%              Number of equality atoms :  220 ( 696 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f812,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f103,f141,f153,f158,f201,f209,f230,f253,f279,f315,f327,f333,f367,f389,f426,f466,f495,f514,f518,f542,f609,f613,f642,f665,f691,f722,f740,f810,f811])).

fof(f811,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK1)) != sK4(sK0,sK1)
    | k1_funct_1(sK1,sK4(sK0,sK1)) != k1_xboole_0
    | ~ r2_hidden(k4_tarski(k1_xboole_0,k1_xboole_0),sK1)
    | r2_hidden(k4_tarski(sK4(sK0,sK1),sK4(sK0,sK1)),sK1) ),
    introduced(theory_axiom,[])).

fof(f810,plain,
    ( spl6_134
    | ~ spl6_48
    | ~ spl6_84
    | ~ spl6_122 ),
    inference(avatar_split_clause,[],[f746,f738,f512,f331,f808])).

fof(f808,plain,
    ( spl6_134
  <=> r2_hidden(k4_tarski(k1_xboole_0,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_134])])).

fof(f331,plain,
    ( spl6_48
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f512,plain,
    ( spl6_84
  <=> k1_funct_1(sK1,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f738,plain,
    ( spl6_122
  <=> r2_hidden(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f746,plain,
    ( r2_hidden(k4_tarski(k1_xboole_0,k1_xboole_0),sK1)
    | ~ spl6_48
    | ~ spl6_84
    | ~ spl6_122 ),
    inference(forward_demodulation,[],[f741,f513])).

fof(f513,plain,
    ( k1_funct_1(sK1,k1_xboole_0) = k1_xboole_0
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f512])).

fof(f741,plain,
    ( r2_hidden(k4_tarski(k1_xboole_0,k1_funct_1(sK1,k1_xboole_0)),sK1)
    | ~ spl6_48
    | ~ spl6_122 ),
    inference(resolution,[],[f739,f332])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) )
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f331])).

fof(f739,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | ~ spl6_122 ),
    inference(avatar_component_clause,[],[f738])).

fof(f740,plain,
    ( spl6_122
    | ~ spl6_88
    | ~ spl6_100
    | spl6_109
    | ~ spl6_114 ),
    inference(avatar_split_clause,[],[f726,f689,f663,f607,f540,f738])).

fof(f540,plain,
    ( spl6_88
  <=> r2_hidden(sK4(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f607,plain,
    ( spl6_100
  <=> k1_funct_1(sK1,sK4(sK0,sK1)) = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f663,plain,
    ( spl6_109
  <=> ~ r2_hidden(k4_tarski(sK4(sK0,sK1),sK4(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).

fof(f689,plain,
    ( spl6_114
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK1)
        | k1_funct_1(sK1,X0) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f726,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | ~ spl6_88
    | ~ spl6_100
    | ~ spl6_109
    | ~ spl6_114 ),
    inference(backward_demodulation,[],[f715,f541])).

fof(f541,plain,
    ( r2_hidden(sK4(sK0,sK1),sK0)
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f540])).

fof(f715,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ spl6_100
    | ~ spl6_109
    | ~ spl6_114 ),
    inference(backward_demodulation,[],[f704,f608])).

fof(f608,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK1)) = sK4(sK0,sK1)
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f607])).

fof(f704,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK1)) = k1_xboole_0
    | ~ spl6_109
    | ~ spl6_114 ),
    inference(resolution,[],[f690,f664])).

fof(f664,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK0,sK1),sK4(sK0,sK1)),sK1)
    | ~ spl6_109 ),
    inference(avatar_component_clause,[],[f663])).

fof(f690,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK1)
        | k1_funct_1(sK1,X0) = k1_xboole_0 )
    | ~ spl6_114 ),
    inference(avatar_component_clause,[],[f689])).

fof(f722,plain,
    ( spl6_118
    | spl6_109
    | ~ spl6_114 ),
    inference(avatar_split_clause,[],[f704,f689,f663,f720])).

fof(f720,plain,
    ( spl6_118
  <=> k1_funct_1(sK1,sK4(sK0,sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f691,plain,
    ( spl6_114
    | ~ spl6_66
    | ~ spl6_82 ),
    inference(avatar_split_clause,[],[f507,f493,f424,f689])).

fof(f424,plain,
    ( spl6_66
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_xboole_0
        | k1_funct_1(sK1,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f493,plain,
    ( spl6_82
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | k1_funct_1(sK1,X0) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f507,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK1)
        | k1_funct_1(sK1,X0) = k1_xboole_0 )
    | ~ spl6_66
    | ~ spl6_82 ),
    inference(duplicate_literal_removal,[],[f502])).

fof(f502,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK1)
        | k1_funct_1(sK1,X0) = k1_xboole_0
        | k1_funct_1(sK1,X0) = k1_xboole_0 )
    | ~ spl6_66
    | ~ spl6_82 ),
    inference(superposition,[],[f494,f425])).

fof(f425,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_xboole_0
        | k1_funct_1(sK1,X0) = X0 )
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f424])).

fof(f494,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | k1_funct_1(sK1,X0) = k1_xboole_0 )
    | ~ spl6_82 ),
    inference(avatar_component_clause,[],[f493])).

fof(f665,plain,
    ( ~ spl6_109
    | ~ spl6_0
    | spl6_11
    | ~ spl6_88
    | ~ spl6_106 ),
    inference(avatar_split_clause,[],[f656,f639,f540,f130,f94,f663])).

fof(f94,plain,
    ( spl6_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f130,plain,
    ( spl6_11
  <=> k6_relat_1(sK0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f639,plain,
    ( spl6_106
  <=> sK4(sK0,sK1) = sK5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f656,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK0,sK1),sK4(sK0,sK1)),sK1)
    | ~ spl6_0
    | ~ spl6_11
    | ~ spl6_88
    | ~ spl6_106 ),
    inference(forward_demodulation,[],[f655,f640])).

fof(f640,plain,
    ( sK4(sK0,sK1) = sK5(sK0,sK1)
    | ~ spl6_106 ),
    inference(avatar_component_clause,[],[f639])).

fof(f655,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ spl6_0
    | ~ spl6_11
    | ~ spl6_88
    | ~ spl6_106 ),
    inference(subsumption_resolution,[],[f654,f95])).

fof(f95,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f94])).

fof(f654,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_11
    | ~ spl6_88
    | ~ spl6_106 ),
    inference(subsumption_resolution,[],[f653,f541])).

fof(f653,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_11
    | ~ spl6_106 ),
    inference(subsumption_resolution,[],[f652,f131])).

fof(f131,plain,
    ( k6_relat_1(sK0) != sK1
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f652,plain,
    ( k6_relat_1(sK0) = sK1
    | ~ r2_hidden(sK4(sK0,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_106 ),
    inference(trivial_inequality_removal,[],[f651])).

fof(f651,plain,
    ( sK4(sK0,sK1) != sK4(sK0,sK1)
    | k6_relat_1(sK0) = sK1
    | ~ r2_hidden(sK4(sK0,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_106 ),
    inference(superposition,[],[f73,f640])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != sK5(X0,X1)
      | k6_relat_1(X0) = X1
      | ~ r2_hidden(sK4(X0,X1),X0)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK4(X0,X1) != sK5(X0,X1)
              | ~ r2_hidden(sK4(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & ( ( sK4(X0,X1) = sK5(X0,X1)
                & r2_hidden(sK4(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK4(X0,X1) != sK5(X0,X1)
          | ~ r2_hidden(sK4(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( ( sK4(X0,X1) = sK5(X0,X1)
            & r2_hidden(sK4(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t34_funct_1.p',d10_relat_1)).

fof(f642,plain,
    ( spl6_106
    | spl6_11
    | ~ spl6_100
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f634,f611,f607,f130,f639])).

fof(f611,plain,
    ( spl6_102
  <=> ! [X0] :
        ( sK4(X0,sK1) = sK5(X0,sK1)
        | k6_relat_1(X0) = sK1
        | k1_funct_1(sK1,sK4(X0,sK1)) = sK5(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f634,plain,
    ( sK4(sK0,sK1) = sK5(sK0,sK1)
    | ~ spl6_11
    | ~ spl6_100
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f630,f131])).

fof(f630,plain,
    ( sK4(sK0,sK1) = sK5(sK0,sK1)
    | k6_relat_1(sK0) = sK1
    | ~ spl6_100
    | ~ spl6_102 ),
    inference(duplicate_literal_removal,[],[f625])).

fof(f625,plain,
    ( sK4(sK0,sK1) = sK5(sK0,sK1)
    | k6_relat_1(sK0) = sK1
    | sK4(sK0,sK1) = sK5(sK0,sK1)
    | ~ spl6_100
    | ~ spl6_102 ),
    inference(superposition,[],[f608,f612])).

fof(f612,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(X0,sK1)) = sK5(X0,sK1)
        | k6_relat_1(X0) = sK1
        | sK4(X0,sK1) = sK5(X0,sK1) )
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f611])).

fof(f613,plain,
    ( spl6_102
    | ~ spl6_46
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f397,f387,f325,f611])).

fof(f325,plain,
    ( spl6_46
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f387,plain,
    ( spl6_58
  <=> ! [X0] :
        ( sK4(X0,sK1) = sK5(X0,sK1)
        | r2_hidden(k4_tarski(sK4(X0,sK1),sK5(X0,sK1)),sK1)
        | k6_relat_1(X0) = sK1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f397,plain,
    ( ! [X0] :
        ( sK4(X0,sK1) = sK5(X0,sK1)
        | k6_relat_1(X0) = sK1
        | k1_funct_1(sK1,sK4(X0,sK1)) = sK5(X0,sK1) )
    | ~ spl6_46
    | ~ spl6_58 ),
    inference(resolution,[],[f388,f326])).

fof(f326,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f325])).

fof(f388,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(X0,sK1),sK5(X0,sK1)),sK1)
        | sK4(X0,sK1) = sK5(X0,sK1)
        | k6_relat_1(X0) = sK1 )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f387])).

fof(f609,plain,
    ( spl6_100
    | spl6_11
    | ~ spl6_16
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f534,f516,f156,f130,f607])).

fof(f156,plain,
    ( spl6_16
  <=> ! [X3] :
        ( k1_funct_1(sK1,X3) = X3
        | ~ r2_hidden(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f516,plain,
    ( spl6_86
  <=> ! [X1] :
        ( r2_hidden(sK4(X1,sK1),X1)
        | k6_relat_1(X1) = sK1
        | r2_hidden(sK4(X1,sK1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f534,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK1)) = sK4(sK0,sK1)
    | ~ spl6_11
    | ~ spl6_16
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f533,f157])).

fof(f157,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | k1_funct_1(sK1,X3) = X3 )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f533,plain,
    ( r2_hidden(sK4(sK0,sK1),sK0)
    | k1_funct_1(sK1,sK4(sK0,sK1)) = sK4(sK0,sK1)
    | ~ spl6_11
    | ~ spl6_16
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f524,f131])).

fof(f524,plain,
    ( r2_hidden(sK4(sK0,sK1),sK0)
    | k6_relat_1(sK0) = sK1
    | k1_funct_1(sK1,sK4(sK0,sK1)) = sK4(sK0,sK1)
    | ~ spl6_16
    | ~ spl6_86 ),
    inference(resolution,[],[f517,f157])).

fof(f517,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(X1,sK1),X1)
        | r2_hidden(sK4(X1,sK1),sK0)
        | k6_relat_1(X1) = sK1 )
    | ~ spl6_86 ),
    inference(avatar_component_clause,[],[f516])).

fof(f542,plain,
    ( spl6_88
    | spl6_11
    | ~ spl6_86 ),
    inference(avatar_split_clause,[],[f535,f516,f130,f540])).

fof(f535,plain,
    ( r2_hidden(sK4(sK0,sK1),sK0)
    | ~ spl6_11
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f530,f131])).

fof(f530,plain,
    ( r2_hidden(sK4(sK0,sK1),sK0)
    | k6_relat_1(sK0) = sK1
    | ~ spl6_86 ),
    inference(factoring,[],[f517])).

fof(f518,plain,
    ( spl6_86
    | ~ spl6_30
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f376,f365,f228,f516])).

fof(f228,plain,
    ( spl6_30
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f365,plain,
    ( spl6_54
  <=> ! [X0] :
        ( r2_hidden(sK4(X0,sK1),X0)
        | r2_hidden(k4_tarski(sK4(X0,sK1),sK5(X0,sK1)),sK1)
        | k6_relat_1(X0) = sK1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f376,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(X1,sK1),X1)
        | k6_relat_1(X1) = sK1
        | r2_hidden(sK4(X1,sK1),sK0) )
    | ~ spl6_30
    | ~ spl6_54 ),
    inference(resolution,[],[f366,f229])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f228])).

fof(f366,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(X0,sK1),sK5(X0,sK1)),sK1)
        | r2_hidden(sK4(X0,sK1),X0)
        | k6_relat_1(X0) = sK1 )
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f365])).

fof(f514,plain,
    ( spl6_84
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f496,f464,f512])).

fof(f464,plain,
    ( spl6_74
  <=> ! [X0] :
        ( k1_xboole_0 != X0
        | k1_funct_1(sK1,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f496,plain,
    ( k1_funct_1(sK1,k1_xboole_0) = k1_xboole_0
    | ~ spl6_74 ),
    inference(equality_resolution,[],[f465])).

fof(f465,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | k1_funct_1(sK1,X0) = X0 )
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f464])).

fof(f495,plain,
    ( spl6_82
    | ~ spl6_42
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f342,f331,f313,f493])).

fof(f313,plain,
    ( spl6_42
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f342,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | k1_funct_1(sK1,X0) = k1_xboole_0 )
    | ~ spl6_42
    | ~ spl6_48 ),
    inference(resolution,[],[f332,f314])).

fof(f314,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = k1_xboole_0 )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f313])).

fof(f466,plain,
    ( spl6_74
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f454,f424,f464])).

fof(f454,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | k1_funct_1(sK1,X0) = X0 )
    | ~ spl6_66 ),
    inference(equality_factoring,[],[f425])).

fof(f426,plain,
    ( spl6_66
    | ~ spl6_16
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f316,f313,f156,f424])).

fof(f316,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_xboole_0
        | k1_funct_1(sK1,X0) = X0 )
    | ~ spl6_16
    | ~ spl6_42 ),
    inference(resolution,[],[f314,f157])).

fof(f389,plain,
    ( spl6_58
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f308,f94,f387])).

fof(f308,plain,
    ( ! [X0] :
        ( sK4(X0,sK1) = sK5(X0,sK1)
        | r2_hidden(k4_tarski(sK4(X0,sK1),sK5(X0,sK1)),sK1)
        | k6_relat_1(X0) = sK1 )
    | ~ spl6_0 ),
    inference(resolution,[],[f72,f95])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | sK4(X0,X1) = sK5(X0,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f367,plain,
    ( spl6_54
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f306,f94,f365])).

fof(f306,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0,sK1),X0)
        | r2_hidden(k4_tarski(sK4(X0,sK1),sK5(X0,sK1)),sK1)
        | k6_relat_1(X0) = sK1 )
    | ~ spl6_0 ),
    inference(resolution,[],[f71,f95])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f333,plain,
    ( spl6_48
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f298,f139,f101,f94,f331])).

fof(f101,plain,
    ( spl6_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f139,plain,
    ( spl6_12
  <=> k1_relat_1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f297,f140])).

fof(f140,plain,
    ( k1_relat_1(sK1) = sK0
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f296,f95])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f84,f102])).

fof(f102,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t34_funct_1.p',d4_funct_1)).

fof(f327,plain,
    ( spl6_46
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f280,f101,f94,f325])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f278,f95])).

fof(f278,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1
        | ~ v1_relat_1(sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f80,f102])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t34_funct_1.p',t8_funct_1)).

fof(f315,plain,
    ( spl6_42
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f275,f139,f101,f94,f313])).

fof(f275,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = k1_xboole_0 )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f274,f140])).

fof(f274,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = k1_xboole_0 )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f273,f95])).

fof(f273,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = k1_xboole_0
        | ~ v1_relat_1(sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f82,f102])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f279,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_26
    | spl6_35 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_26
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f95,f102,f252,f208,f80])).

fof(f208,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),sK1)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl6_26
  <=> r2_hidden(k4_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f252,plain,
    ( k1_funct_1(sK1,sK2) != sK2
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl6_35
  <=> k1_funct_1(sK1,sK2) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f253,plain,
    ( ~ spl6_11
    | ~ spl6_35
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f231,f139,f251,f130])).

fof(f231,plain,
    ( k1_funct_1(sK1,sK2) != sK2
    | k6_relat_1(sK0) != sK1
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f57,f140])).

fof(f57,plain,
    ( k1_funct_1(sK1,sK2) != sK2
    | k1_relat_1(sK1) != sK0
    | k6_relat_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ( k1_funct_1(sK1,sK2) != sK2
        & r2_hidden(sK2,sK0) )
      | k1_relat_1(sK1) != sK0
      | k6_relat_1(sK0) != sK1 )
    & ( ( ! [X3] :
            ( k1_funct_1(sK1,X3) = X3
            | ~ r2_hidden(X3,sK0) )
        & k1_relat_1(sK1) = sK0 )
      | k6_relat_1(sK0) = sK1 )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0
          | k6_relat_1(X0) != X1 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) = X1 )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ? [X2] :
            ( k1_funct_1(sK1,X2) != X2
            & r2_hidden(X2,sK0) )
        | k1_relat_1(sK1) != sK0
        | k6_relat_1(sK0) != sK1 )
      & ( ( ! [X3] :
              ( k1_funct_1(sK1,X3) = X3
              | ~ r2_hidden(X3,sK0) )
          & k1_relat_1(sK1) = sK0 )
        | k6_relat_1(sK0) = sK1 )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK2) != sK2
        & r2_hidden(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = X3
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k6_relat_1(X0) = X1
        <=> ( ! [X2] :
                ( r2_hidden(X2,X0)
               => k1_funct_1(X1,X2) = X2 )
            & k1_relat_1(X1) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t34_funct_1.p',t34_funct_1)).

fof(f230,plain,
    ( spl6_30
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f226,f139,f101,f94,f228])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f225,f140])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f224,f95])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f79,f102])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f209,plain,
    ( spl6_26
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f199,f151,f133,f207])).

fof(f133,plain,
    ( spl6_10
  <=> k6_relat_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f151,plain,
    ( spl6_14
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f199,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),sK1)
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f198,f134])).

fof(f134,plain,
    ( k6_relat_1(sK0) = sK1
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f198,plain,
    ( r2_hidden(k4_tarski(sK2,sK2),k6_relat_1(sK0))
    | ~ spl6_14 ),
    inference(resolution,[],[f189,f152])).

fof(f152,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f189,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,X0)
      | r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f86,f59])).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t34_funct_1.p',dt_k6_relat_1)).

fof(f86,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f201,plain,
    ( spl6_12
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f174,f133,f139])).

fof(f174,plain,
    ( k1_relat_1(sK1) = sK0
    | ~ spl6_10 ),
    inference(superposition,[],[f60,f134])).

fof(f60,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t34_funct_1.p',t71_relat_1)).

fof(f158,plain,
    ( spl6_16
    | spl6_11 ),
    inference(avatar_split_clause,[],[f154,f130,f156])).

fof(f154,plain,
    ( ! [X3] :
        ( k1_funct_1(sK1,X3) = X3
        | ~ r2_hidden(X3,sK0) )
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f55,f131])).

fof(f55,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = X3
      | ~ r2_hidden(X3,sK0)
      | k6_relat_1(sK0) = sK1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f153,plain,
    ( ~ spl6_11
    | spl6_14
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f146,f139,f151,f130])).

fof(f146,plain,
    ( r2_hidden(sK2,sK0)
    | k6_relat_1(sK0) != sK1
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f56,f140])).

fof(f56,plain,
    ( r2_hidden(sK2,sK0)
    | k1_relat_1(sK1) != sK0
    | k6_relat_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f141,plain,
    ( spl6_10
    | spl6_12 ),
    inference(avatar_split_clause,[],[f54,f139,f133])).

fof(f54,plain,
    ( k1_relat_1(sK1) = sK0
    | k6_relat_1(sK0) = sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f53,f101])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f52,f94])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
