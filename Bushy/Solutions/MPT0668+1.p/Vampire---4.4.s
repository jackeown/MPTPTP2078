%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t85_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:28 EDT 2019

% Result     : Theorem 4.52s
% Output     : Refutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  277 ( 787 expanded)
%              Number of leaves         :   71 ( 365 expanded)
%              Depth                    :   17
%              Number of atoms          : 1177 (5726 expanded)
%              Number of equality atoms :  164 ( 972 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f132,f136,f140,f141,f142,f149,f153,f157,f161,f165,f169,f173,f177,f271,f301,f337,f341,f347,f356,f380,f392,f408,f468,f488,f492,f623,f1468,f1481,f1492,f1496,f1500,f1509,f1541,f1546,f1624,f8709,f8726,f8744,f8753,f8774,f8802,f8882,f8895,f9996,f10985,f10986,f10995,f11016,f11063,f11069,f11079,f11132])).

fof(f11132,plain,
    ( ~ spl11_1121
    | spl11_382
    | ~ spl11_16
    | ~ spl11_1106 ),
    inference(avatar_split_clause,[],[f11123,f8623,f155,f1563,f8704])).

fof(f8704,plain,
    ( spl11_1121
  <=> ~ r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1121])])).

fof(f1563,plain,
    ( spl11_382
  <=> r2_hidden(sK7(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_382])])).

fof(f155,plain,
    ( spl11_16
  <=> ! [X6] :
        ( r2_hidden(k1_funct_1(sK2,X6),sK0)
        | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f8623,plain,
    ( spl11_1106
  <=> k1_funct_1(sK2,sK6(sK0,sK2,sK1)) = sK7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1106])])).

fof(f11123,plain,
    ( r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl11_16
    | ~ spl11_1106 ),
    inference(superposition,[],[f156,f8624])).

fof(f8624,plain,
    ( k1_funct_1(sK2,sK6(sK0,sK2,sK1)) = sK7(sK0,sK2,sK1)
    | ~ spl11_1106 ),
    inference(avatar_component_clause,[],[f8623])).

fof(f156,plain,
    ( ! [X6] :
        ( r2_hidden(k1_funct_1(sK2,X6),sK0)
        | ~ r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f11079,plain,
    ( spl11_396
    | ~ spl11_1132
    | ~ spl11_1136 ),
    inference(avatar_split_clause,[],[f11078,f8751,f8742,f8843])).

fof(f8843,plain,
    ( spl11_396
  <=> r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_396])])).

fof(f8742,plain,
    ( spl11_1132
  <=> k1_funct_1(sK1,sK6(sK0,sK2,sK1)) = sK7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1132])])).

fof(f8751,plain,
    ( spl11_1136
  <=> r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_funct_1(sK1,sK6(sK0,sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1136])])).

fof(f11078,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1)
    | ~ spl11_1132
    | ~ spl11_1136 ),
    inference(forward_demodulation,[],[f8752,f8743])).

fof(f8743,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK2,sK1)) = sK7(sK0,sK2,sK1)
    | ~ spl11_1132 ),
    inference(avatar_component_clause,[],[f8742])).

fof(f8752,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_funct_1(sK1,sK6(sK0,sK2,sK1))),sK1)
    | ~ spl11_1136 ),
    inference(avatar_component_clause,[],[f8751])).

fof(f11069,plain,
    ( spl11_1106
    | spl11_0
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_70
    | spl11_397 ),
    inference(avatar_split_clause,[],[f10810,f1619,f335,f175,f167,f144,f8623])).

fof(f144,plain,
    ( spl11_0
  <=> k8_relat_1(sK0,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f167,plain,
    ( spl11_22
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f175,plain,
    ( spl11_26
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f335,plain,
    ( spl11_70
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | k1_funct_1(sK2,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f1619,plain,
    ( spl11_397
  <=> ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_397])])).

fof(f10810,plain,
    ( k8_relat_1(sK0,sK2) = sK1
    | k1_funct_1(sK2,sK6(sK0,sK2,sK1)) = sK7(sK0,sK2,sK1)
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_70
    | ~ spl11_397 ),
    inference(resolution,[],[f1620,f2818])).

fof(f2818,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK6(X0,sK2,sK1),sK7(X0,sK2,sK1)),sK1)
        | k8_relat_1(X0,sK2) = sK1
        | k1_funct_1(sK2,sK6(X0,sK2,sK1)) = sK7(X0,sK2,sK1) )
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_70 ),
    inference(resolution,[],[f1400,f336])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | k1_funct_1(sK2,X0) = X1 )
    | ~ spl11_70 ),
    inference(avatar_component_clause,[],[f335])).

fof(f1400,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK6(X0,sK2,sK1),sK7(X0,sK2,sK1)),sK2)
        | k8_relat_1(X0,sK2) = sK1
        | r2_hidden(k4_tarski(sK6(X0,sK2,sK1),sK7(X0,sK2,sK1)),sK1) )
    | ~ spl11_22
    | ~ spl11_26 ),
    inference(resolution,[],[f1091,f168])).

fof(f168,plain,
    ( v1_relat_1(sK2)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f167])).

fof(f1091,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK6(X2,X3,sK1),sK7(X2,X3,sK1)),sK1)
        | k8_relat_1(X2,X3) = sK1
        | r2_hidden(k4_tarski(sK6(X2,X3,sK1),sK7(X2,X3,sK1)),X3) )
    | ~ spl11_26 ),
    inference(resolution,[],[f87,f176])).

fof(f176,plain,
    ( v1_relat_1(sK1)
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f175])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK7(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
                    & r2_hidden(sK7(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',d12_relat_1)).

fof(f1620,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1)
    | ~ spl11_397 ),
    inference(avatar_component_clause,[],[f1619])).

fof(f11063,plain,
    ( spl11_0
    | spl11_1128
    | spl11_1140
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_1118 ),
    inference(avatar_split_clause,[],[f11062,f8694,f175,f167,f8781,f8724,f144])).

fof(f8724,plain,
    ( spl11_1128
  <=> r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1128])])).

fof(f8781,plain,
    ( spl11_1140
  <=> r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1140])])).

fof(f8694,plain,
    ( spl11_1118
  <=> k1_xboole_0 = sK7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1118])])).

fof(f11062,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | k8_relat_1(sK0,sK2) = sK1
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_1118 ),
    inference(forward_demodulation,[],[f11055,f8695])).

fof(f8695,plain,
    ( k1_xboole_0 = sK7(sK0,sK2,sK1)
    | ~ spl11_1118 ),
    inference(avatar_component_clause,[],[f8694])).

fof(f11055,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | k8_relat_1(sK0,sK2) = sK1
    | r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1)
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_1118 ),
    inference(superposition,[],[f1400,f8695])).

fof(f11016,plain,
    ( spl11_1472
    | ~ spl11_1128 ),
    inference(avatar_split_clause,[],[f8819,f8724,f10979])).

fof(f10979,plain,
    ( spl11_1472
  <=> r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1472])])).

fof(f8819,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2))
    | ~ spl11_1128 ),
    inference(resolution,[],[f8725,f107])).

fof(f107,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f54,f57,f56,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',d4_relat_1)).

fof(f8725,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | ~ spl11_1128 ),
    inference(avatar_component_clause,[],[f8724])).

fof(f10995,plain,
    ( spl11_382
    | spl11_0
    | ~ spl11_22
    | ~ spl11_26
    | spl11_397 ),
    inference(avatar_split_clause,[],[f10811,f1619,f175,f167,f144,f1563])).

fof(f10811,plain,
    ( k8_relat_1(sK0,sK2) = sK1
    | r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | ~ spl11_22
    | ~ spl11_26
    | ~ spl11_397 ),
    inference(resolution,[],[f1620,f1265])).

fof(f1265,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK6(X0,sK2,sK1),sK7(X0,sK2,sK1)),sK1)
        | k8_relat_1(X0,sK2) = sK1
        | r2_hidden(sK7(X0,sK2,sK1),X0) )
    | ~ spl11_22
    | ~ spl11_26 ),
    inference(resolution,[],[f878,f168])).

fof(f878,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK6(X2,X3,sK1),sK7(X2,X3,sK1)),sK1)
        | k8_relat_1(X2,X3) = sK1
        | r2_hidden(sK7(X2,X3,sK1),X2) )
    | ~ spl11_26 ),
    inference(resolution,[],[f86,f176])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f10986,plain,
    ( spl11_1472
    | spl11_1118
    | ~ spl11_60
    | ~ spl11_1106 ),
    inference(avatar_split_clause,[],[f10971,f8623,f299,f8694,f10979])).

fof(f299,plain,
    ( spl11_60
  <=> ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f10971,plain,
    ( k1_xboole_0 = sK7(sK0,sK2,sK1)
    | r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2))
    | ~ spl11_60
    | ~ spl11_1106 ),
    inference(superposition,[],[f300,f8624])).

fof(f300,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) = k1_xboole_0
        | r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl11_60 ),
    inference(avatar_component_clause,[],[f299])).

fof(f10985,plain,
    ( spl11_1120
    | ~ spl11_1473
    | ~ spl11_383
    | ~ spl11_14
    | ~ spl11_1106 ),
    inference(avatar_split_clause,[],[f10968,f8623,f151,f8865,f10983,f8697])).

fof(f8697,plain,
    ( spl11_1120
  <=> r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1120])])).

fof(f10983,plain,
    ( spl11_1473
  <=> ~ r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1473])])).

fof(f8865,plain,
    ( spl11_383
  <=> ~ r2_hidden(sK7(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_383])])).

fof(f151,plain,
    ( spl11_14
  <=> ! [X6] :
        ( r2_hidden(X6,k1_relat_1(sK1))
        | ~ r2_hidden(X6,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X6),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f10968,plain,
    ( ~ r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2))
    | r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl11_14
    | ~ spl11_1106 ),
    inference(superposition,[],[f152,f8624])).

fof(f152,plain,
    ( ! [X6] :
        ( ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
        | ~ r2_hidden(X6,k1_relat_1(sK2))
        | r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f9996,plain,
    ( spl11_4
    | ~ spl11_360 ),
    inference(avatar_split_clause,[],[f9985,f1494,f134])).

fof(f134,plain,
    ( spl11_4
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1494,plain,
    ( spl11_360
  <=> r2_hidden(k4_tarski(sK4,sK10(sK1,sK4)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_360])])).

fof(f9985,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl11_360 ),
    inference(resolution,[],[f1495,f107])).

fof(f1495,plain,
    ( r2_hidden(k4_tarski(sK4,sK10(sK1,sK4)),sK2)
    | ~ spl11_360 ),
    inference(avatar_component_clause,[],[f1494])).

fof(f8895,plain,
    ( spl11_1120
    | ~ spl11_396 ),
    inference(avatar_split_clause,[],[f8852,f8843,f8697])).

fof(f8852,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl11_396 ),
    inference(resolution,[],[f8844,f107])).

fof(f8844,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1)
    | ~ spl11_396 ),
    inference(avatar_component_clause,[],[f8843])).

fof(f8882,plain,
    ( spl11_1132
    | ~ spl11_72
    | ~ spl11_396 ),
    inference(avatar_split_clause,[],[f8851,f8843,f339,f8742])).

fof(f339,plain,
    ( spl11_72
  <=> ! [X3,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f8851,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK2,sK1)) = sK7(sK0,sK2,sK1)
    | ~ spl11_72
    | ~ spl11_396 ),
    inference(resolution,[],[f8844,f340])).

fof(f340,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3 )
    | ~ spl11_72 ),
    inference(avatar_component_clause,[],[f339])).

fof(f8802,plain,
    ( spl11_1106
    | ~ spl11_12
    | ~ spl11_1120
    | ~ spl11_1132 ),
    inference(avatar_split_clause,[],[f8801,f8742,f8697,f147,f8623])).

fof(f147,plain,
    ( spl11_12
  <=> ! [X5] :
        ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
        | ~ r2_hidden(X5,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f8801,plain,
    ( k1_funct_1(sK2,sK6(sK0,sK2,sK1)) = sK7(sK0,sK2,sK1)
    | ~ spl11_12
    | ~ spl11_1120
    | ~ spl11_1132 ),
    inference(forward_demodulation,[],[f8793,f8743])).

fof(f8793,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK2,sK1)) = k1_funct_1(sK2,sK6(sK0,sK2,sK1))
    | ~ spl11_12
    | ~ spl11_1120 ),
    inference(resolution,[],[f8698,f148])).

fof(f148,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK1))
        | k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5) )
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f8698,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl11_1120 ),
    inference(avatar_component_clause,[],[f8697])).

fof(f8774,plain,
    ( ~ spl11_1141
    | spl11_397
    | ~ spl11_1118 ),
    inference(avatar_split_clause,[],[f8759,f8694,f1619,f8772])).

fof(f8772,plain,
    ( spl11_1141
  <=> ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1141])])).

fof(f8759,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | ~ spl11_397
    | ~ spl11_1118 ),
    inference(superposition,[],[f1620,f8695])).

fof(f8753,plain,
    ( spl11_1136
    | ~ spl11_120
    | ~ spl11_1120 ),
    inference(avatar_split_clause,[],[f8731,f8697,f490,f8751])).

fof(f490,plain,
    ( spl11_120
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_120])])).

fof(f8731,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_funct_1(sK1,sK6(sK0,sK2,sK1))),sK1)
    | ~ spl11_120
    | ~ spl11_1120 ),
    inference(resolution,[],[f8698,f491])).

fof(f491,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1) )
    | ~ spl11_120 ),
    inference(avatar_component_clause,[],[f490])).

fof(f8744,plain,
    ( spl11_1132
    | ~ spl11_12
    | ~ spl11_1106
    | ~ spl11_1120 ),
    inference(avatar_split_clause,[],[f8740,f8697,f8623,f147,f8742])).

fof(f8740,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK2,sK1)) = sK7(sK0,sK2,sK1)
    | ~ spl11_12
    | ~ spl11_1106
    | ~ spl11_1120 ),
    inference(forward_demodulation,[],[f8729,f8624])).

fof(f8729,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK2,sK1)) = k1_funct_1(sK2,sK6(sK0,sK2,sK1))
    | ~ spl11_12
    | ~ spl11_1120 ),
    inference(resolution,[],[f8698,f148])).

fof(f8726,plain,
    ( spl11_1128
    | ~ spl11_398
    | ~ spl11_1118 ),
    inference(avatar_split_clause,[],[f8722,f8694,f8707,f8724])).

fof(f8707,plain,
    ( spl11_398
  <=> r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_398])])).

fof(f8722,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | ~ spl11_398
    | ~ spl11_1118 ),
    inference(forward_demodulation,[],[f8708,f8695])).

fof(f8708,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK2)
    | ~ spl11_398 ),
    inference(avatar_component_clause,[],[f8707])).

fof(f8709,plain,
    ( ~ spl11_1121
    | spl11_398
    | ~ spl11_18
    | ~ spl11_118
    | ~ spl11_1106 ),
    inference(avatar_split_clause,[],[f8686,f8623,f486,f159,f8707,f8704])).

fof(f159,plain,
    ( spl11_18
  <=> ! [X6] :
        ( r2_hidden(X6,k1_relat_1(sK2))
        | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f486,plain,
    ( spl11_118
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_118])])).

fof(f8686,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK2)
    | ~ r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl11_18
    | ~ spl11_118
    | ~ spl11_1106 ),
    inference(superposition,[],[f1608,f8624])).

fof(f1608,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl11_18
    | ~ spl11_118 ),
    inference(resolution,[],[f160,f487])).

fof(f487,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) )
    | ~ spl11_118 ),
    inference(avatar_component_clause,[],[f486])).

fof(f160,plain,
    ( ! [X6] :
        ( r2_hidden(X6,k1_relat_1(sK2))
        | ~ r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f1624,plain,
    ( ~ spl11_23
    | ~ spl11_27
    | ~ spl11_397
    | spl11_0
    | ~ spl11_399
    | ~ spl11_382 ),
    inference(avatar_split_clause,[],[f1615,f1563,f1622,f144,f1619,f303,f296])).

fof(f296,plain,
    ( spl11_23
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f303,plain,
    ( spl11_27
  <=> ~ v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f1622,plain,
    ( spl11_399
  <=> ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_399])])).

fof(f1615,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK2)
    | k8_relat_1(sK0,sK2) = sK1
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl11_382 ),
    inference(resolution,[],[f1564,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
      | k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1564,plain,
    ( r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | ~ spl11_382 ),
    inference(avatar_component_clause,[],[f1563])).

fof(f1546,plain,
    ( k1_funct_1(sK1,sK4) != sK10(sK1,sK4)
    | k1_funct_1(sK1,sK4) != k1_funct_1(sK2,sK4)
    | r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | ~ r2_hidden(sK10(sK1,sK4),sK0) ),
    introduced(theory_axiom,[])).

fof(f1541,plain,
    ( spl11_44
    | ~ spl11_70
    | ~ spl11_366 ),
    inference(avatar_split_clause,[],[f1536,f1507,f335,f241])).

fof(f241,plain,
    ( spl11_44
  <=> k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f1507,plain,
    ( spl11_366
  <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_366])])).

fof(f1536,plain,
    ( k1_funct_1(sK1,sK4) = k1_funct_1(sK2,sK4)
    | ~ spl11_70
    | ~ spl11_366 ),
    inference(resolution,[],[f1508,f336])).

fof(f1508,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2)
    | ~ spl11_366 ),
    inference(avatar_component_clause,[],[f1507])).

fof(f1509,plain,
    ( spl11_366
    | ~ spl11_360
    | ~ spl11_362 ),
    inference(avatar_split_clause,[],[f1505,f1498,f1494,f1507])).

fof(f1498,plain,
    ( spl11_362
  <=> k1_funct_1(sK1,sK4) = sK10(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_362])])).

fof(f1505,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2)
    | ~ spl11_360
    | ~ spl11_362 ),
    inference(forward_demodulation,[],[f1495,f1499])).

fof(f1499,plain,
    ( k1_funct_1(sK1,sK4) = sK10(sK1,sK4)
    | ~ spl11_362 ),
    inference(avatar_component_clause,[],[f1498])).

fof(f1500,plain,
    ( spl11_362
    | ~ spl11_72
    | ~ spl11_356 ),
    inference(avatar_split_clause,[],[f1485,f1479,f339,f1498])).

fof(f1479,plain,
    ( spl11_356
  <=> r2_hidden(k4_tarski(sK4,sK10(sK1,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_356])])).

fof(f1485,plain,
    ( k1_funct_1(sK1,sK4) = sK10(sK1,sK4)
    | ~ spl11_72
    | ~ spl11_356 ),
    inference(resolution,[],[f1480,f340])).

fof(f1480,plain,
    ( r2_hidden(k4_tarski(sK4,sK10(sK1,sK4)),sK1)
    | ~ spl11_356 ),
    inference(avatar_component_clause,[],[f1479])).

fof(f1496,plain,
    ( spl11_360
    | ~ spl11_78
    | ~ spl11_356 ),
    inference(avatar_split_clause,[],[f1484,f1479,f354,f1494])).

fof(f354,plain,
    ( spl11_78
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f1484,plain,
    ( r2_hidden(k4_tarski(sK4,sK10(sK1,sK4)),sK2)
    | ~ spl11_78
    | ~ spl11_356 ),
    inference(resolution,[],[f1480,f355])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X0,X1),sK2) )
    | ~ spl11_78 ),
    inference(avatar_component_clause,[],[f354])).

fof(f1492,plain,
    ( spl11_358
    | ~ spl11_156
    | ~ spl11_356 ),
    inference(avatar_split_clause,[],[f1483,f1479,f621,f1490])).

fof(f1490,plain,
    ( spl11_358
  <=> r2_hidden(sK10(sK1,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_358])])).

fof(f621,plain,
    ( spl11_156
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_156])])).

fof(f1483,plain,
    ( r2_hidden(sK10(sK1,sK4),sK0)
    | ~ spl11_156
    | ~ spl11_356 ),
    inference(resolution,[],[f1480,f622])).

fof(f622,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,sK0) )
    | ~ spl11_156 ),
    inference(avatar_component_clause,[],[f621])).

fof(f1481,plain,
    ( spl11_356
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f1471,f127,f1479])).

fof(f127,plain,
    ( spl11_2
  <=> r2_hidden(sK4,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f1471,plain,
    ( r2_hidden(k4_tarski(sK4,sK10(sK1,sK4)),sK1)
    | ~ spl11_2 ),
    inference(resolution,[],[f128,f108])).

fof(f108,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f128,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f1468,plain,
    ( ~ spl11_7
    | ~ spl11_0
    | spl11_3
    | ~ spl11_22
    | ~ spl11_92
    | ~ spl11_110 ),
    inference(avatar_split_clause,[],[f1467,f466,f406,f167,f114,f144,f120])).

fof(f120,plain,
    ( spl11_7
  <=> ~ r2_hidden(k1_funct_1(sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f114,plain,
    ( spl11_3
  <=> ~ r2_hidden(sK4,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f406,plain,
    ( spl11_92
  <=> r2_hidden(k4_tarski(sK4,sK10(sK2,sK4)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_92])])).

fof(f466,plain,
    ( spl11_110
  <=> k1_funct_1(sK2,sK4) = sK10(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_110])])).

fof(f1467,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_22
    | ~ spl11_92
    | ~ spl11_110 ),
    inference(forward_demodulation,[],[f1465,f467])).

fof(f467,plain,
    ( k1_funct_1(sK2,sK4) = sK10(sK2,sK4)
    | ~ spl11_110 ),
    inference(avatar_component_clause,[],[f466])).

fof(f1465,plain,
    ( ~ r2_hidden(sK10(sK2,sK4),sK0)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_22
    | ~ spl11_92 ),
    inference(resolution,[],[f1461,f407])).

fof(f407,plain,
    ( r2_hidden(k4_tarski(sK4,sK10(sK2,sK4)),sK2)
    | ~ spl11_92 ),
    inference(avatar_component_clause,[],[f406])).

fof(f1461,plain,
    ( ! [X11] :
        ( ~ r2_hidden(k4_tarski(sK4,X11),sK2)
        | ~ r2_hidden(X11,sK0) )
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_22 ),
    inference(resolution,[],[f1455,f115])).

fof(f115,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK1))
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1455,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl11_0
    | ~ spl11_22 ),
    inference(superposition,[],[f1445,f145])).

fof(f145,plain,
    ( k8_relat_1(sK0,sK2) = sK1
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f144])).

fof(f1445,plain,
    ( ! [X6,X8,X7] :
        ( r2_hidden(X8,k1_relat_1(k8_relat_1(X7,sK2)))
        | ~ r2_hidden(k4_tarski(X8,X6),sK2)
        | ~ r2_hidden(X6,X7) )
    | ~ spl11_22 ),
    inference(resolution,[],[f1440,f107])).

fof(f1440,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X2,X0),k8_relat_1(X1,sK2))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) )
    | ~ spl11_22 ),
    inference(resolution,[],[f809,f168])).

fof(f809,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f807])).

fof(f807,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f104,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',dt_k8_relat_1)).

fof(f104,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f623,plain,
    ( ~ spl11_23
    | spl11_156
    | ~ spl11_27
    | ~ spl11_0 ),
    inference(avatar_split_clause,[],[f619,f144,f303,f621,f296])).

fof(f619,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,sK0)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_0 ),
    inference(forward_demodulation,[],[f618,f145])).

fof(f618,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,sK0)
        | ~ v1_relat_1(k8_relat_1(sK0,sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl11_0 ),
    inference(superposition,[],[f106,f145])).

fof(f106,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f492,plain,
    ( ~ spl11_27
    | spl11_120
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f484,f171,f490,f303])).

fof(f171,plain,
    ( spl11_24
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f484,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl11_24 ),
    inference(resolution,[],[f103,f172])).

fof(f172,plain,
    ( v1_funct_1(sK1)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f171])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',d4_funct_1)).

fof(f488,plain,
    ( ~ spl11_23
    | spl11_118
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f483,f163,f486,f296])).

fof(f163,plain,
    ( spl11_20
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f483,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_20 ),
    inference(resolution,[],[f103,f164])).

fof(f164,plain,
    ( v1_funct_1(sK2)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f163])).

fof(f468,plain,
    ( spl11_110
    | ~ spl11_70
    | ~ spl11_92 ),
    inference(avatar_split_clause,[],[f461,f406,f335,f466])).

fof(f461,plain,
    ( k1_funct_1(sK2,sK4) = sK10(sK2,sK4)
    | ~ spl11_70
    | ~ spl11_92 ),
    inference(resolution,[],[f407,f336])).

fof(f408,plain,
    ( spl11_92
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f402,f134,f406])).

fof(f402,plain,
    ( r2_hidden(k4_tarski(sK4,sK10(sK2,sK4)),sK2)
    | ~ spl11_4 ),
    inference(resolution,[],[f135,f108])).

fof(f135,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f392,plain,
    ( spl11_8
    | ~ spl11_70
    | ~ spl11_84 ),
    inference(avatar_split_clause,[],[f387,f378,f335,f226])).

fof(f226,plain,
    ( spl11_8
  <=> k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f378,plain,
    ( spl11_84
  <=> r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f387,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl11_70
    | ~ spl11_84 ),
    inference(resolution,[],[f379,f336])).

fof(f379,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK2)
    | ~ spl11_84 ),
    inference(avatar_component_clause,[],[f378])).

fof(f380,plain,
    ( spl11_84
    | ~ spl11_50
    | ~ spl11_74
    | ~ spl11_78 ),
    inference(avatar_split_clause,[],[f376,f354,f345,f269,f378])).

fof(f269,plain,
    ( spl11_50
  <=> r2_hidden(k4_tarski(sK3,sK10(sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f345,plain,
    ( spl11_74
  <=> k1_funct_1(sK1,sK3) = sK10(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f376,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK2)
    | ~ spl11_50
    | ~ spl11_74
    | ~ spl11_78 ),
    inference(forward_demodulation,[],[f373,f346])).

fof(f346,plain,
    ( k1_funct_1(sK1,sK3) = sK10(sK1,sK3)
    | ~ spl11_74 ),
    inference(avatar_component_clause,[],[f345])).

fof(f373,plain,
    ( r2_hidden(k4_tarski(sK3,sK10(sK1,sK3)),sK2)
    | ~ spl11_50
    | ~ spl11_78 ),
    inference(resolution,[],[f355,f270])).

fof(f270,plain,
    ( r2_hidden(k4_tarski(sK3,sK10(sK1,sK3)),sK1)
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f269])).

fof(f356,plain,
    ( ~ spl11_23
    | spl11_78
    | ~ spl11_0 ),
    inference(avatar_split_clause,[],[f352,f144,f354,f296])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_0 ),
    inference(superposition,[],[f182,f145])).

fof(f182,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f82,f105])).

fof(f105,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f347,plain,
    ( spl11_74
    | ~ spl11_50
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f342,f339,f269,f345])).

fof(f342,plain,
    ( k1_funct_1(sK1,sK3) = sK10(sK1,sK3)
    | ~ spl11_50
    | ~ spl11_72 ),
    inference(resolution,[],[f340,f270])).

fof(f341,plain,
    ( ~ spl11_27
    | spl11_72
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f333,f171,f339,f303])).

fof(f333,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3
        | ~ v1_relat_1(sK1) )
    | ~ spl11_24 ),
    inference(resolution,[],[f99,f172])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',t8_funct_1)).

fof(f337,plain,
    ( ~ spl11_23
    | spl11_70
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f332,f163,f335,f296])).

fof(f332,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | k1_funct_1(sK2,X0) = X1
        | ~ v1_relat_1(sK2) )
    | ~ spl11_20 ),
    inference(resolution,[],[f99,f164])).

fof(f301,plain,
    ( ~ spl11_23
    | spl11_60
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f293,f163,f299,f296])).

fof(f293,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_xboole_0
        | ~ v1_relat_1(sK2) )
    | ~ spl11_20 ),
    inference(resolution,[],[f101,f164])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f271,plain,
    ( spl11_50
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f265,f138,f269])).

fof(f138,plain,
    ( spl11_10
  <=> r2_hidden(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f265,plain,
    ( r2_hidden(k4_tarski(sK3,sK10(sK1,sK3)),sK1)
    | ~ spl11_10 ),
    inference(resolution,[],[f108,f139])).

fof(f139,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f177,plain,(
    spl11_26 ),
    inference(avatar_split_clause,[],[f61,f175])).

fof(f61,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
        & r2_hidden(sK3,k1_relat_1(sK1)) )
      | ( ( ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
          | ~ r2_hidden(sK4,k1_relat_1(sK2))
          | ~ r2_hidden(sK4,k1_relat_1(sK1)) )
        & ( ( r2_hidden(k1_funct_1(sK2,sK4),sK0)
            & r2_hidden(sK4,k1_relat_1(sK2)) )
          | r2_hidden(sK4,k1_relat_1(sK1)) ) )
      | k8_relat_1(sK0,sK2) != sK1 )
    & ( ( ! [X5] :
            ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
            | ~ r2_hidden(X5,k1_relat_1(sK1)) )
        & ! [X6] :
            ( ( r2_hidden(X6,k1_relat_1(sK1))
              | ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
              | ~ r2_hidden(X6,k1_relat_1(sK2)) )
            & ( ( r2_hidden(k1_funct_1(sK2,X6),sK0)
                & r2_hidden(X6,k1_relat_1(sK2)) )
              | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ) )
      | k8_relat_1(sK0,sK2) = sK1 )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f39,f43,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) )
              | k8_relat_1(X0,X2) != X1 )
            & ( ( ! [X5] :
                    ( k1_funct_1(X1,X5) = k1_funct_1(X2,X5)
                    | ~ r2_hidden(X5,k1_relat_1(X1)) )
                & ! [X6] :
                    ( ( r2_hidden(X6,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                      | ~ r2_hidden(X6,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                        & r2_hidden(X6,k1_relat_1(X2)) )
                      | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) = X1 )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(sK1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relat_1(sK1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),sK0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(sK1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),sK0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(sK1)) ) )
            | k8_relat_1(sK0,X2) != sK1 )
          & ( ( ! [X5] :
                  ( k1_funct_1(sK1,X5) = k1_funct_1(X2,X5)
                  | ~ r2_hidden(X5,k1_relat_1(sK1)) )
              & ! [X6] :
                  ( ( r2_hidden(X6,k1_relat_1(sK1))
                    | ~ r2_hidden(k1_funct_1(X2,X6),sK0)
                    | ~ r2_hidden(X6,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X6),sK0)
                      & r2_hidden(X6,k1_relat_1(X2)) )
                    | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ) )
            | k8_relat_1(sK0,X2) = sK1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(X1)) ) )
            | k8_relat_1(X0,X2) != X1 )
          & ( ( ! [X5] :
                  ( k1_funct_1(X1,X5) = k1_funct_1(X2,X5)
                  | ~ r2_hidden(X5,k1_relat_1(X1)) )
              & ! [X6] :
                  ( ( r2_hidden(X6,k1_relat_1(X1))
                    | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                    | ~ r2_hidden(X6,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                      & r2_hidden(X6,k1_relat_1(X2)) )
                    | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
            | k8_relat_1(X0,X2) = X1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ( ? [X3] :
              ( k1_funct_1(sK2,X3) != k1_funct_1(X1,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | ? [X4] :
              ( ( ~ r2_hidden(k1_funct_1(sK2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(sK2))
                | ~ r2_hidden(X4,k1_relat_1(X1)) )
              & ( ( r2_hidden(k1_funct_1(sK2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(sK2)) )
                | r2_hidden(X4,k1_relat_1(X1)) ) )
          | k8_relat_1(X0,sK2) != X1 )
        & ( ( ! [X5] :
                ( k1_funct_1(sK2,X5) = k1_funct_1(X1,X5)
                | ~ r2_hidden(X5,k1_relat_1(X1)) )
            & ! [X6] :
                ( ( r2_hidden(X6,k1_relat_1(X1))
                  | ~ r2_hidden(k1_funct_1(sK2,X6),X0)
                  | ~ r2_hidden(X6,k1_relat_1(sK2)) )
                & ( ( r2_hidden(k1_funct_1(sK2,X6),X0)
                    & r2_hidden(X6,k1_relat_1(sK2)) )
                  | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
          | k8_relat_1(X0,sK2) = X1 )
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK3) != k1_funct_1(X2,sK3)
        & r2_hidden(sK3,k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
            | ~ r2_hidden(X4,k1_relat_1(X2))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X2,sK4),X0)
          | ~ r2_hidden(sK4,k1_relat_1(X2))
          | ~ r2_hidden(sK4,k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X2,sK4),X0)
            & r2_hidden(sK4,k1_relat_1(X2)) )
          | r2_hidden(sK4,k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(X1)) ) )
            | k8_relat_1(X0,X2) != X1 )
          & ( ( ! [X5] :
                  ( k1_funct_1(X1,X5) = k1_funct_1(X2,X5)
                  | ~ r2_hidden(X5,k1_relat_1(X1)) )
              & ! [X6] :
                  ( ( r2_hidden(X6,k1_relat_1(X1))
                    | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                    | ~ r2_hidden(X6,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                      & r2_hidden(X6,k1_relat_1(X2)) )
                    | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
            | k8_relat_1(X0,X2) = X1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(X1)) ) )
            | k8_relat_1(X0,X2) != X1 )
          & ( ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( ( r2_hidden(X4,k1_relat_1(X1))
                    | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
            | k8_relat_1(X0,X2) = X1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(X1)) ) )
            | k8_relat_1(X0,X2) != X1 )
          & ( ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( ( r2_hidden(X4,k1_relat_1(X1))
                    | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
            | k8_relat_1(X0,X2) = X1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <~> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <~> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( k8_relat_1(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
                & ! [X4] :
                    ( r2_hidden(X4,k1_relat_1(X1))
                  <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( k8_relat_1(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
                & ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                  <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                      & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',t85_funct_1)).

fof(f173,plain,(
    spl11_24 ),
    inference(avatar_split_clause,[],[f62,f171])).

fof(f62,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f169,plain,(
    spl11_22 ),
    inference(avatar_split_clause,[],[f63,f167])).

fof(f63,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f165,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f64,f163])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f161,plain,
    ( spl11_0
    | spl11_18 ),
    inference(avatar_split_clause,[],[f65,f159,f144])).

fof(f65,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_relat_1(sK2))
      | ~ r2_hidden(X6,k1_relat_1(sK1))
      | k8_relat_1(sK0,sK2) = sK1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f157,plain,
    ( spl11_0
    | spl11_16 ),
    inference(avatar_split_clause,[],[f66,f155,f144])).

fof(f66,plain,(
    ! [X6] :
      ( r2_hidden(k1_funct_1(sK2,X6),sK0)
      | ~ r2_hidden(X6,k1_relat_1(sK1))
      | k8_relat_1(sK0,sK2) = sK1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f153,plain,
    ( spl11_0
    | spl11_14 ),
    inference(avatar_split_clause,[],[f67,f151,f144])).

fof(f67,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_relat_1(sK1))
      | ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
      | ~ r2_hidden(X6,k1_relat_1(sK2))
      | k8_relat_1(sK0,sK2) = sK1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f149,plain,
    ( spl11_0
    | spl11_12 ),
    inference(avatar_split_clause,[],[f68,f147,f144])).

fof(f68,plain,(
    ! [X5] :
      ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
      | ~ r2_hidden(X5,k1_relat_1(sK1))
      | k8_relat_1(sK0,sK2) = sK1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f142,plain,
    ( ~ spl11_1
    | spl11_2
    | spl11_4
    | spl11_10 ),
    inference(avatar_split_clause,[],[f69,f138,f134,f127,f111])).

fof(f111,plain,
    ( spl11_1
  <=> k8_relat_1(sK0,sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f69,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK2))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | k8_relat_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f141,plain,
    ( ~ spl11_1
    | spl11_2
    | spl11_6
    | spl11_10 ),
    inference(avatar_split_clause,[],[f70,f138,f130,f127,f111])).

fof(f130,plain,
    ( spl11_6
  <=> r2_hidden(k1_funct_1(sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f70,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | r2_hidden(sK4,k1_relat_1(sK1))
    | k8_relat_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f140,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | spl11_10 ),
    inference(avatar_split_clause,[],[f71,f138,f120,f117,f114,f111])).

fof(f117,plain,
    ( spl11_5
  <=> ~ r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f71,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r2_hidden(sK4,k1_relat_1(sK1))
    | k8_relat_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f136,plain,
    ( ~ spl11_1
    | spl11_2
    | spl11_4
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f72,f123,f134,f127,f111])).

fof(f123,plain,
    ( spl11_9
  <=> k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f72,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | r2_hidden(sK4,k1_relat_1(sK2))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | k8_relat_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f132,plain,
    ( ~ spl11_1
    | spl11_2
    | spl11_6
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f73,f123,f130,f127,f111])).

fof(f73,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | r2_hidden(sK4,k1_relat_1(sK1))
    | k8_relat_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f125,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f74,f123,f120,f117,f114,f111])).

fof(f74,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r2_hidden(sK4,k1_relat_1(sK1))
    | k8_relat_1(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
